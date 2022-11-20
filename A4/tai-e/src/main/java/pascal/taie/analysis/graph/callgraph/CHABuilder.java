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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.exp.InvokeInterface;
import pascal.taie.ir.exp.InvokeSpecial;
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.language.type.ClassType;
import soot.jimple.SpecialInvokeExpr;

import java.util.*;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Queue<JMethod> workList = new LinkedBlockingQueue<>();
        workList.add(entry);

        while (!workList.isEmpty()) {
            JMethod m = workList.remove();
            if (callGraph.contains(m)) continue;

            callGraph.addReachableMethod(m);
            callGraph.callSitesIn(m).forEach(invoke -> resolve(invoke).forEach(mp -> {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, mp));
                workList.add(mp);
            }));
        }

        return callGraph;
    }

    private Set<JClass> getAllSubClassesOf(JClass cls) {
        Set<JClass> res = new HashSet<>(hierarchy.getDirectSubclassesOf(cls));
        Set<JClass> tmp = new HashSet<>();
        for (JClass c : res) {
            Collection<JClass> directSubclasses = hierarchy.getDirectSubclassesOf(c);
            if (!directSubclasses.isEmpty())
                tmp.addAll(getAllSubClassesOf(c));
        }
        res.addAll(tmp);
        return res;
    }

    private Set<JClass> getAllSubInterfacesOf(JClass cls) {
        Set<JClass> res = new HashSet<>(hierarchy.getDirectSubinterfacesOf(cls));
        Set<JClass> tmp = new HashSet<>();
        for (JClass c : res) {
            Collection<JClass> directSubInterfaces = hierarchy.getDirectSubinterfacesOf(c);
            if (!directSubInterfaces.isEmpty())
                tmp.addAll(getAllSubInterfacesOf(c));
        }
        res.addAll(tmp);
        return res;
    }

    private Set<JClass> getAllImplementorsOf(JClass cls) {
        Set<JClass> sub = new HashSet<>(getAllSubInterfacesOf(cls));
        Set<JClass> res = new HashSet<>(hierarchy.getDirectImplementorsOf(cls));
        for (JClass c : sub) {
            res.addAll(getAllImplementorsOf(c));
        }
        return res;
    }

    private JClass getClassOfVar(Var v) {
        assert v.getType() instanceof ClassType;
        return ((ClassType) v.getType()).getJClass();
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> res = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature m = methodRef.getSubsignature();

        if (callSite.isStatic() || callSite.isSpecial()) {
            JClass cm = methodRef.getDeclaringClass();
            res.add(dispatch(cm, m));
        } else if (callSite.isVirtual()){
            JClass c = getClassOfVar(((InvokeVirtual) (callSite.getInvokeExp())).getBase());
            Set<JClass> subClasses = getAllSubClassesOf(c);
            subClasses.add(c);
            for (JClass cp : subClasses) {
                JMethod dispatch = dispatch(cp, m);
                if (dispatch != null)
                    res.add(dispatch);
            }
        } else if (callSite.isInterface()) {
            JClass c = getClassOfVar(((InvokeInterface) (callSite.getInvokeExp())).getBase());
            Set<JClass> implementors = getAllImplementorsOf(c);
            for (JClass cp : implementors) {
                JMethod dispatch = dispatch(cp, m);
                if (dispatch != null)
                    res.add(dispatch);
            }
        }

        return res;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        for (JMethod m : jclass.getDeclaredMethods()) {
            if (!m.isAbstract()
                    && m.getSubsignature().toString().equals(subsignature.toString()))
                return m;
        }

        if (jclass.getSuperClass() != null)
            return dispatch(jclass.getSuperClass(), subsignature);

        else
            return null;
    }
}
