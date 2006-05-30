/*
 * Created on 20 sept. 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.modifexpression;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.formula.Predicate0Ar;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Nothing extends ModifiesExpression {
	public static Nothing NOTHING = new Nothing();
	
	private Nothing() {}
	
	public String toString() {
		return "\\nothing";
	}

	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getPostCondition()
	 */
	public Expression getPostCondition(IJml2bConfiguration config, int state) {
		return Predicate0Ar.TRUE;
	}

	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getExpression()
	 */
	public Expression getExpression() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		// TODO Auto-generated method stub
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return this;
	}


}
