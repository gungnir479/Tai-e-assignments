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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.Edge;

import java.util.concurrent.LinkedBlockingQueue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        LinkedBlockingQueue<Node> workList = new LinkedBlockingQueue<>();
        cfg.getNodes().forEach(n -> { if (!cfg.isEntry(n)) workList.add(n); });
        while (!workList.isEmpty()) {
            Node cur = workList.remove();
            Fact inFact = result.getInFact(cur);
            Fact outFact = result.getOutFact(cur);

            cfg.getInEdgesOf(cur).forEach(e -> {
                Fact out = result.getOutFact(e.getSource());
                analysis.meetInto(out, inFact);
            });
            if (analysis.transferNode(cur, inFact, outFact)) {
                cfg.getOutEdgesOf(cur).forEach(e -> {
                    if (!workList.contains(e.getTarget()))
                        workList.add(e.getTarget());
                });
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        LinkedBlockingQueue<Node> workList = new LinkedBlockingQueue<>();
        cfg.getNodes().forEach(n -> { if (!cfg.isExit(n)) workList.add(n); });
        while (!workList.isEmpty()) {
            Node cur = workList.remove();
            Fact inFact = result.getInFact(cur);
            Fact outFact = result.getOutFact(cur);

            for (Edge<Node> e : cfg.getOutEdgesOf(cur)) {
                Fact in = result.getInFact(e.getTarget());
                analysis.meetInto(in, outFact);
            }
            if (analysis.transferNode(cur, inFact, outFact)) {
                cfg.getInEdgesOf(cur).forEach(e -> {
                    if (!workList.contains(e.getSource()))
                        workList.add(e.getSource());
                });
            }
        }
    }
}
