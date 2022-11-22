/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (!callGraph.contains(csMethod)) return;

        List<Stmt> stmts = csMethod.getMethod().getIR().getStmts();
        for (Stmt stmt : stmts) {
            Context c = csMethod.getContext();
            if (stmt instanceof New s) {
                CSVar csVar = csManager.getCSVar(c, s.getLValue());
                Obj obj = heapModel.getObj(s);
                Context context = contextSelector.selectHeapContext(csMethod, obj);
                PointsToSet objs = PointsToSetFactory.make(csManager.getCSObj(context, obj));
                workList.addEntry(csVar, objs);
            } else if (stmt instanceof Copy s) {
                CSVar l = csManager.getCSVar(c, s.getLValue());
                CSVar r = csManager.getCSVar(c, s.getRValue());
                addPFGEdge(r, l);
            } else if (stmt instanceof StoreField s && s.isStatic()) {
                StaticField staticField = csManager.getStaticField(s.getFieldRef().resolve());
                CSVar csVar = csManager.getCSVar(c, s.getRValue());
                addPFGEdge(csVar, staticField);
            } else if (stmt instanceof LoadField s && s.isStatic()) {
                StaticField staticField = csManager.getStaticField(s.getFieldRef().resolve());
                CSVar varPtr = csManager.getCSVar(c, s.getLValue());
                addPFGEdge(staticField, varPtr);
            } else if (stmt instanceof Invoke s && s.isStatic()) {
                Context ct = contextSelector.selectContext(csManager.getCSCallSite(c, s), resolveCallee(null, s));
//                todo
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.addEdge(source, target)) return;

        PointsToSet srcPt = source.getPointsToSet();
        if (!srcPt.isEmpty())
            workList.addEntry(target, srcPt);
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            PointsToSet diff = propagate(n, pts);

            if (n instanceof CSVar csVar_) {
                Var var = csVar_.getVar();
                Context c = csVar_.getContext();
                for (CSObj obj : diff) {
                    for (StoreField stmt : var.getStoreFields()) {
                        InstanceField field = csManager.getInstanceField(obj, stmt.getFieldRef().resolve());
                        CSVar csVar = csManager.getCSVar(c, stmt.getRValue());
                        addPFGEdge(csVar, field);
                    }

                    for (LoadField stmt : var.getLoadFields()) {
                        InstanceField field = csManager.getInstanceField(obj, stmt.getFieldRef().resolve());
                        CSVar csVar = csManager.getCSVar(c, stmt.getLValue());
                        addPFGEdge(field, csVar);
                    }

                    for (StoreArray stmt : var.getStoreArrays()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        CSVar csVar = csManager.getCSVar(c, stmt.getRValue());
                        addPFGEdge(csVar, arrayIndex);
                    }

                    for (LoadArray stmt : var.getLoadArrays()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        CSVar csVar = csManager.getCSVar(c, stmt.getLValue());
                        addPFGEdge(csVar, arrayIndex);
                    }

                    processCall(csVar_, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        if (pointsToSet.isEmpty()) return pointsToSet;

        PointsToSet diff = PointsToSetFactory.make();
        PointsToSet n = pointer.getPointsToSet();
        pointsToSet.objects().forEach(o -> {
            if (!n.contains(o)) {
                n.addObject(o);
                diff.addObject(o);
            }
        });
        if (!diff.isEmpty())
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer))
                workList.addEntry(succ, diff);
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        Context c = recv.getContext();
        Context cp = recvObj.getContext();

        for (Invoke l : recv.getVar().getInvokes()) {
            JMethod m = resolveCallee(recvObj, l);
            Context ct = contextSelector.selectContext(csManager.getCSCallSite(c, l), recvObj, m);
            workList.addEntry(csManager.getCSVar(ct, m.getIR().getThis()), PointsToSetFactory.make(recvObj));
            processCall(csManager.getCSMethod(ct, m), csManager.getCSCallSite(c, l));
        }
    }

    private void processCall(CSMethod m, CSCallSite l) {
        if (!callGraph.addEdge(new Edge<>(getCallKind(l.getCallSite()), l, m)))
            return;

        Context ct = m.getContext();
        Context c = l.getContext();
        List<Var> params = m.getMethod().getIR().getParams();
        List<Var> args = l.getCallSite().getInvokeExp().getArgs();

        addReachable(m);
        for (int i=0; i< args.size(); i++)
            addPFGEdge(csManager.getCSVar(c, args.get(i)), csManager.getCSVar(ct, params.get(i)));

        Var lValue = l.getCallSite().getLValue();

        if (lValue != null) {
            List<Var> returnVars = m.getMethod().getIR().getReturnVars();
            for (Var ret : returnVars)
                addPFGEdge(csManager.getCSVar(ct, ret), csManager.getCSVar(c, lValue));
        }
    }

    private static CallKind getCallKind(Invoke callSite) {
        if (callSite.isStatic()) return CallKind.STATIC;
        else if (callSite.isSpecial()) return CallKind.SPECIAL;
        else if (callSite.isVirtual()) return CallKind.VIRTUAL;
        else if (callSite.isSpecial()) return CallKind.SPECIAL;
        else if (callSite.isInterface()) return CallKind.INTERFACE;
        else if (callSite.isDynamic()) return CallKind.DYNAMIC;
        else return CallKind.OTHER;
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
