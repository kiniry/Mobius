/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package formula;

import bcexpression.Expression;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class QuantifiedFormula extends Formula {
	private Quantificator[] quantificators;
	/*private Formula subformula;
*/

	
	public QuantifiedFormula(Formula _formula, Quantificator _q) {
		super(_formula);
		quantificators = new Quantificator[]{_q};
	}

	public QuantifiedFormula(Formula _formula, Quantificator[] _q) {
		super(_formula);
		quantificators = _q;
	}

	/**
	 * quantifies the formula over the expression  _q 
	 * @param _q
	 * @return true and quantifies if the formula is not uop to now quantified 
	 * false - if it is already quantified over the expression and  does the quantification 
	 *//*
	public boolean addQuantificator(Quantificator _q) {
		// verify if it is not already quantified over the same variable
		for (int i = 0; i < quantificators.length; i++) {
			Quantificator q =  quantificators[i];
			if (q.getBoundVar().equals( _q) ) {
				return false;
			}
		} 	
		Quantificator[] _quantificators = quantificators;
		quantificators = new Quantificator[quantificators.length + 1];
		for (int i = 0; i < _quantificators.length; i++) {
			quantificators[i] =  _quantificators[i];
		}
		quantificators[quantificators.length - 1] = _q;
		return true;
	}*/
	
	/**
	 * @return Returns the quantificator.
	 */
	public Quantificator getQuantificator() {
		return quantificators[0];
	}

	/**
	 * @return Returns the quantificator.
	 */
	public Quantificator[] getQuantificators() {
		return quantificators;
	}

	public Expression copy() {
		Formula subformula = (Formula)getSubExpressions()[0];
		Formula _subformula = (Formula)subformula.copy();
		Quantificator[] q = new Quantificator[quantificators.length];
		for (int i = 0; i < quantificators.length; i++) {
			q[i] = (Quantificator)quantificators[i].copy();
		}
		Formula _copy = new QuantifiedFormula(_subformula, q);
		return _copy;
	}

	public String toString() {
		Formula subformula = (Formula)getSubExpressions()[0];
		String s = "";
		for (int i = 0; i < quantificators.length; i++) {
			s = s + quantificators[i];
		}
		s = s + subformula;
		return s;
	}
	/**
	 * the renaming actually here is a special substition which affects also  variables under quantifiction 
	 * rename expr1 by expr2
	 * Renaming must be done in such a way that no capture of variables should be done , i.e. the expr2 must be a fresh variable 
	 */
	public Expression rename(Expression expr1, Expression expr2) {
		for (int i = 0; i < quantificators.length; i++) {
			Expression[] boundExpr = quantificators[i].getBoundVars();
			for (int j = 0; j < boundExpr.length; j++) {
				if (expr1.equals(boundExpr[i])) {
					boundExpr[i] = boundExpr[i].rename(expr1, expr2);
				}
			}
			quantificators[i].setBoundVars(boundExpr);
		}
		Expression[] subformula = getSubExpressions();
		subformula[0] = subformula[0].rename(expr1, expr2);
	
		return this;
	}
	
	/**
	 * substition  is realised iff the expression that should be substituted  - _e
	 * is not under quantification. If it is not the substitution continues recursively
	 * 
	 * @return the substituted formula
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		//Util.dump(toString());
		for (int i = 0; i < quantificators.length; i++) {
			/*Expression boundExpr = quantificators[i].getBoundVar();
			if (_e.equals(boundExpr)) {
				return this;
			}*/
			quantificators[i].substitute(_e1, _e2);
		}
		Expression[] subformula = getSubExpressions();
		subformula[0] = subformula[0].substitute(_e1,_e2);
		return this;
	}
	
	public boolean equals(Formula formula) {
		boolean eq = super.equals( formula);
		if ( ! eq ) {
			return false;
		}
		if ( ! (formula instanceof QuantifiedFormula )) {
			return false;
		} 
		/*Formula f = (Formula)getSubExpressions()[0];
		Formula _f = (Formula)formula.getSubExpressions()[0];
		 eq = f.equals(_f);*/
		Quantificator[] _q =  ((QuantifiedFormula)formula).getQuantificators();
		if (_q.length != quantificators.length) {
			return false;
		}
		for (int i = 0; i < quantificators.length; i++) {
			if (! quantificators[i].equals( _q[i])) {
				return false;
			}
		}
		return true;
	}
}
