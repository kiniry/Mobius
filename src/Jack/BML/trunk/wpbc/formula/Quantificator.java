/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Quantificator extends Expression {
	public static final String FORALL = "forall";
	public static final String EXISTS = "exists";

	private Expression boundVar;
	private String quantifier;
	private Expression domain;

	public Quantificator(String _quantifier, Expression _boundVar) {
		quantifier = _quantifier;
		setBoundVar(_boundVar);
	}

	public Quantificator(
		String _quantifier,
		Expression _boundVar,
		Expression _domain) {
		this(_quantifier, _boundVar);
		domain = _domain;
	}

	//	public void addBoundVar(Vector var)  {
	//		if (bound_vars == null) {
	//			bound_vars = new Vector();
	//		}
	//		bound_vars.add(var);
	//	}

	public void dump() {

	}

	public Expression copy() {
		return this;
	}
	
//	public Expression substitute( Expression _e, Expression _v ) {
//		return null;
//	}

	public boolean equals(Quantificator quantificator) {
		if (!quantificator.getBoundVar().equals(getBoundVar()) ) {
			return false;
		}
		if (!quantificator.getQuantifier().equals(getQuantifier()) ) {
			return false;
		}
		if (!quantificator.getDomain().equals(getDomain()) ) {
			return false;
		}
		return true;
		
	}
	
	public String toString( ) {
		if (domain == null) {
			return  "(" + quantifier + "  " + boundVar + "  )";
		}
		return  "(" + quantifier + "  " + boundVar +  "."+ domain.toString() + ")";
	}

	/**
	 * @return
	 */
	public Expression getBoundVar() {
		return boundVar;
	}

	/**
	 * @param expression
	 */
	public void setBoundVar(Expression expression) {
		boundVar = expression;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (boundVar.equals(_e1) ) {
			return this;
		}
		if (domain != null) {
			domain = domain.substitute(_e1, _e2);
		}
		return this;
	}

	/**
	 * @return Returns the domain.
	 */
	public Expression getDomain() {
		return domain;
	}
	/**
	 * @return Returns the quantifier.
	 */
	public String getQuantifier() {
		return quantifier;
	}
}
