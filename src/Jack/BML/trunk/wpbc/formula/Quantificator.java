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
public class Quantificator {
	public static final String FORALL = "forall";
	public static final String EXISTS = "exists";

	private Expression boundVar;
	private String quantifier;
	private Formula domain;

	public Quantificator(String _quantifier, Expression _boundVar) {
		quantifier = _quantifier;
		boundVar = _boundVar;
	}

	public Quantificator(
		String _quantifier,
		Expression _boundVar,
		Formula _domain) {
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

	public Quantificator substitute(Expression _e, Expression _o) {
		return null;
	}
	
	public Quantificator copy( ) {
		return null;
	}

}
