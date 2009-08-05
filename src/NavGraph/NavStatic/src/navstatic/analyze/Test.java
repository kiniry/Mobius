package navstatic.analyze;

import java.util.ArrayList;
import java.util.List;

import soot.Local;
import soot.PointsToSet;
import soot.RefType;
import soot.Unit;
import soot.Value;
import soot.jimple.BinopExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceOfExpr;
import soot.jimple.IntConstant;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;

public class Test {
	final String symbol;
	final AbsValue arg1;
	final AbsValue arg2;
	Test(PathAnalysis pa, IfStmt stmt) {
		Value expr = stmt.getCondition();
		if (expr instanceof BinopExpr) {
			BinopExpr bexpr = (BinopExpr) expr;
			arg1 = AbsValue.makeDisj(analyzeArg(pa, bexpr.getOp1(), stmt));
			arg2 = AbsValue.makeDisj(analyzeArg(pa, bexpr.getOp2(), stmt));
			symbol = bexpr.getSymbol().trim();
		} else if (expr instanceof InstanceOfExpr) {
			InstanceOfExpr iexpr = (InstanceOfExpr) expr;
			arg1 = AbsValue.makeDisj(analyzeArg(pa, iexpr.getOp(), stmt));
			arg2 = new AbsValue.AbsString(iexpr.getType().toString());
			symbol = "instanceof";
		} else {
			symbol = expr.toString().trim();
			arg1 = null;
			arg2 = null;
		}
	}
	
	List <AbsValue> analyzeArg(PathAnalysis pa, Value expr, Stmt stmt) {
		List <AbsValue> result = new ArrayList<AbsValue> ();
		if (expr instanceof Local) {
			List <Unit> defs = pa.defuse.getDefsOfAt((Local) expr, stmt);
			for (Unit u : defs) {
				if(u instanceof DefinitionStmt) {
					Value defexpr = ((DefinitionStmt) u).getRightOp();
					List <AbsValue> res = analyzeArg(pa,defexpr,(Stmt) u);
					if (res == null) {
						if (defexpr.getType() instanceof RefType) {
							PointsToSet pts = pa.context.pag.reachingObjects((Local) expr);
							AbsValue values = PointstoExplorer.contents(pa.context, pts);
							result.add(values);
						} else {
							result.add(new AbsValue.AbsUnknown(defexpr.toString()));
						}
					} else result.addAll(res);
				}
			}		
		} else if (expr instanceof ParameterRef) {
			result.add(new AbsValue.AbsParam(((ParameterRef) expr).getIndex() + 1));
		} else if (expr instanceof ThisRef) {
			result.add(new AbsValue.AbsParam(0));
		} else if (expr instanceof StringConstant){
			result.add(new AbsValue.AbsString(((StringConstant) expr).value));
		} else if (expr instanceof IntConstant){
			result.add(new AbsValue.AbsInteger(((IntConstant) expr).value));	
		} else {
			return null;
		}
		return result;
	}
	
	public String toString() {
		StringBuffer buf = new StringBuffer();
		buf.append("<test symbol=\"" + Explorer.htmlProtect(symbol) + "\">");
		if (arg1 != null) buf.append(arg1);
		if (arg2 != null) buf.append(arg2);
		buf.append("</test>");
		return buf.toString();
	}
	
}
