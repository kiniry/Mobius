package mobius.directVCGen.formula.jmlTranslator;

import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import escjava.sortedProver.Lifter.Term;
import javafe.ast.BinaryExpr;

public class JmlExprToFormula {

	JmlVisitor v;
	
	public JmlExprToFormula(JmlVisitor visitor) {
		v = visitor;
	}

	public Term add(BinaryExpr expr) {
		Term t1 = (Term)expr.left.accept(v,null);
		Term t2 = (Term)expr.right.accept(v,null);
		return Num.add(t1, t2);
	}

}
