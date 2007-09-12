package annot.formula;

import annot.bcclass.BMLConfig;

public class QuantifiedFormula extends Formula {
	private Quantificator[] quantificators;

	/*
	 * private Formula subformula;
	 */

	public QuantifiedFormula(Formula _formula, Quantificator _q) {
		super(_formula);
		quantificators = new Quantificator[] { _q };
		priority = 17; //?
	}

	public QuantifiedFormula(Formula _formula, Quantificator[] _q) {
		super(_formula);
		quantificators = _q;
		priority = 17; //?
	}

//	/**
//	 * quantifies the formula over the expression _q
//	 * 
//	 * @param _q
//	 * @return true and quantifies if the formula is not uop to now quantified
//	 *         false - if it is already quantified over the expression and does
//	 *         the quantification
//	 */
//
//	/**
//	 * @return Returns the quantificator.
//	 */
//	public Quantificator getQuantificator() {
//		return quantificators[0];
//	}
//
//	/**
//	 * @return Returns the quantificator.
//	 */
//	public Quantificator[] getQuantificators() {
//		return quantificators;
//	}
//
//	public Expression copy() {
//		Formula subformula = (Formula) getSubExpressions()[0];
//		Formula _subformula = (Formula) subformula.copy();
//		Quantificator[] q = new Quantificator[quantificators.length];
//		for (int i = 0; i < quantificators.length; i++) {
//			q[i] = (Quantificator) quantificators[i].copy();
//		}
//		Formula _copy = new QuantifiedFormula(_subformula, q);
//		return _copy;
//	}

	public String printCode1(BMLConfig conf) {
		boolean go3args = true; // makes operator display as 3-arg. instead of binary
		Formula subformula = (Formula) getSubExpressions()[0];
		String s = "";
		for (int i = 0; i < quantificators.length; i++) {
			if (i > 0)
				s += " ";
			s = s + quantificators[i].printCode(conf);
		}
		String sub = subformula.printCode(conf);
		if (go3args)
			sub = sub.substring(1, sub.length()-1);
		s = s + " " + sub;
		return s;
	}
//	/**
//	 * the renaming actually here is a special substition which affects also
//	 * variables under quantifiction rename expr1 by expr2 Renaming must be done
//	 * in such a way that no capture of variables should be done , i.e. the
//	 * expr2 must be a fresh variable
//	 */
//	public Expression rename(Expression expr1, Expression expr2) {
//		for (int i = 0; i < quantificators.length; i++) {
//			Expression[] boundExpr = quantificators[i].getBoundVars();
//			for (int j = 0; j < boundExpr.length; j++) {
//				if (expr1.equals(boundExpr[i])) {
//					boundExpr[i] = boundExpr[i].rename(expr1, expr2);
//				}
//			}
//			quantificators[i].setBoundVars(boundExpr);
//		}
//		Expression[] subformula = getSubExpressions();
//		subformula[0] = subformula[0].rename(expr1, expr2);
//
//		return this;
//	}
//
//	/**
//	 * substition is realised iff the expression that should be substituted - _e
//	 * is not under quantification. If it is not the substitution continues
//	 * recursively
//	 * 
//	 * @return the substituted formula
//	 */
//	public Expression substitute(Expression _e1, Expression _e2) {
//		// Util.dump(toString());
//		// checks if _e1 is a bound variable in this quantified formula. If
//		// it is detected that _e1 is a bound variable in this quantified
//		// formula
//		// return this formula without substitution
//		for (int i = 0; i < quantificators.length; i++) {
//			Expression[] boundExpr = quantificators[i].getBoundVars();
//			for (int s = 0; s < boundExpr.length; s++) {
//				if (_e1.equals(boundExpr[s])) {
//					return this;
//				}
//			}
//			/* quantificators[i].substitute(_e1, _e2); */
//		}
//		Expression[] subformula = getSubExpressions();
//		// Expression f = subformula[0].copy();
//
//		subformula[0] = subformula[0].substitute(_e1, _e2);
//		return this;
//	}
//
//	public boolean equals(Formula formula) {
//		boolean eq = super.equals(formula);
//		if (!eq) {
//			return false;
//		}
//		if (!(formula instanceof QuantifiedFormula)) {
//			return false;
//		}
//		/*
//		 * Formula f = (Formula)getSubExpressions()[0]; Formula _f =
//		 * (Formula)formula.getSubExpressions()[0]; eq = f.equals(_f);
//		 */
//		Quantificator[] _q = ((QuantifiedFormula) formula).getQuantificators();
//		if (_q.length != quantificators.length) {
//			return false;
//		}
//		for (int i = 0; i < quantificators.length; i++) {
//			if (!quantificators[i].equals(_q[i])) {
//				return false;
//			}
//		}
//		return true;
//	}
//
//
//	public Expression simplify() {
//		Expression[] subFromulas = getSubExpressions();
//		subFromulas[0] = ((Formula) subFromulas[0]).simplify();
//		if (subFromulas[0] == Predicate0Ar.TRUE) {
//			return Predicate0Ar.TRUE;
//		}
//		return this;
//		
//	}
}
