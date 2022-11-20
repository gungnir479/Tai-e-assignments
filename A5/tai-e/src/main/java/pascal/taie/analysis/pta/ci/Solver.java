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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Set<Stmt> reachableStmts = new HashSet<>();

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (!callGraph.addReachableMethod(method)) return;

        List<Stmt> stmts = method.getIR().getStmts();
        reachableStmts.addAll(stmts);
        for (Stmt stmt : stmts) {
            if (stmt instanceof New callSite) {
                VarPtr varPtr = pointerFlowGraph.getVarPtr(callSite.getLValue());
                PointsToSet objs = new PointsToSet(heapModel.getObj(callSite));
                workList.addEntry(varPtr, objs);
            } else if (stmt instanceof Copy callSite) {
                VarPtr l = pointerFlowGraph.getVarPtr(callSite.getLValue());
                VarPtr r = pointerFlowGraph.getVarPtr(callSite.getRValue());
                addPFGEdge(r, l);
            } else if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                StaticField staticField = pointerFlowGraph.getStaticField(storeField.getFieldRef().resolve());
                VarPtr varPtr = pointerFlowGraph.getVarPtr(storeField.getRValue());
                addPFGEdge(varPtr, staticField);
            } else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                StaticField staticField = pointerFlowGraph.getStaticField(loadField.getFieldRef().resolve());
                VarPtr varPtr = pointerFlowGraph.getVarPtr(loadField.getLValue());
                addPFGEdge(staticField, varPtr);
            } else if (stmt instanceof Invoke invoke && invoke.isStatic()) {
                processCall(invoke.getMethodRef().resolve(), invoke);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
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
            if (n instanceof VarPtr var_) {
                Var var = var_.getVar();
                for (Obj obj : diff) {
                    for (StoreField stmt : var.getStoreFields()) {
                        InstanceField field = pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve());
                        VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                        addPFGEdge(varPtr, field);
                    }

                    for (LoadField stmt : var.getLoadFields()) {
                        InstanceField field = pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve());
                        VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                        addPFGEdge(field, varPtr);
                    }

                    for (StoreArray stmt : var.getStoreArrays()) {
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                        addPFGEdge(varPtr, arrayIndex);
                    }

                    for (LoadArray stmt : var.getLoadArrays()) {
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                        addPFGEdge(arrayIndex, varPtr);
                    }

                    processCall(var, obj);
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

        PointsToSet diff = new PointsToSet();
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        List<Invoke> invokes = var.getInvokes();
        for (Invoke invoke : invokes) {
            JMethod m = resolveCallee(recv, invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));

            processCall(m, invoke);
        }
    }

    private void processCall(JMethod m, Invoke callSite) {
        if (!callGraph.addEdge(new Edge<>(getCallKind(callSite), callSite, m)))
            return;

        addReachable(m);
        List<Var> args = callSite.getInvokeExp().getArgs();
        List<Var> params = m.getIR().getParams();
        for (int i=0; i<args.size(); i++)
            addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));

        Var lValue = callSite.getLValue();
        if (lValue != null) {
            List<Var> returnVars = m.getIR().getReturnVars();
            for (Var var : returnVars)
                addPFGEdge(pointerFlowGraph.getVarPtr(var), pointerFlowGraph.getVarPtr(lValue));
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
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
