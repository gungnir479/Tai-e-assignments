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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Map;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact res = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        if (!params.isEmpty()) params.forEach(p -> res.update(p, Value.getNAC()));
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach(e -> target.update(e.getKey(), meetValue(e.getValue(), target.get(e.getKey()))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (v1.getConstant() == v2.getConstant()) return v1;
        return Value.getNAC();
    }

    public static boolean canDeal(Stmt stmt) {
        if (!(stmt instanceof DefinitionStmt defStmt)) return false;
        return defStmt.getLValue() instanceof Var var && canHoldInt(var);
    }

    public static boolean isChanged(CPFact in, CPFact out) {
        Set<Var> inVars = in.keySet();
        Set<Var> outVars = out.keySet();
        if (!inVars.containsAll(outVars) || !outVars.containsAll(inVars)) return true;
        for (Var v : inVars) if (!(in.get(v).equals(out.get(v)))) return true;
        return false;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact copy = out.copy();
        out.clear();
        out.copyFrom(in);

        if (!canDeal(stmt)) return isChanged(out, copy);

        DefinitionStmt defStmt = (DefinitionStmt) stmt;
        Var def = (Var) defStmt.getLValue();
        Value val = evaluate(defStmt.getRValue(), in);
        out.update(def, val);
        return isChanged(out, copy);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            return in.get(var);
        } else if (exp instanceof IntLiteral cons) {
            return Value.makeConstant(cons.getValue());
        } else if (exp instanceof BinaryExp binExp) {
            Value op1 = in.get(binExp.getOperand1());
            Value op2 = in.get(binExp.getOperand2());
            if (op1.isNAC() || op2.isNAC()) return Value.getNAC();
            if (op1.isUndef() || op2.isUndef()) return Value.getUndef();
            if (op1.isConstant() && op2.isConstant()) {
                int con1 = op1.getConstant();
                int con2 = op2.getConstant();
                int res = 0;
                if (exp instanceof ArithmeticExp arithmeticExp) {
                    res = switch (arithmeticExp.getOperator()){
                        case ADD -> con1+con2;
                        case SUB -> con1-con2;
                        case MUL -> con1*con2;
                        case REM -> con1%con2;
                        case DIV -> con1/con2;
                    };
                } else if (exp instanceof ConditionExp conditionExp) {
                    res = switch (conditionExp.getOperator()) {
                        case EQ -> con1==con2?1:0;
                        case GE -> con1>=con2?1:0;
                        case GT -> con1>con2?1:0;
                        case LE -> con1<=con2?1:0;
                        case LT -> con1<con2?1:0;
                        case NE -> con1!=con2?1:0;
                    };
                } else if (exp instanceof ShiftExp shiftExp) {
                    res = switch (shiftExp.getOperator()) {
                        case SHL -> con1<<con2;
                        case SHR -> con1>>con2;
                        case USHR -> con1>>>con2;
                    };
                } else if (exp instanceof BitwiseExp bitwiseExp) {
                    res = switch (bitwiseExp.getOperator()) {
                        case OR -> con1|con2;
                        case AND -> con1&con2;
                        case XOR -> con1^con2;
                    };
                }
                return Value.makeConstant(res);
            }
        }
        return Value.getNAC();
    }
}
