/*
 * Created on Mar 21, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bcexpression.jml;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class SET extends JMLExpression {
	
	public SET( Expression expr1, Expression expr2) {
		super(expr1, expr2 );
		
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		// TODO Auto-generated method stub
		return "set " + getSubExpressions()[0] + " = " + getSubExpressions()[1];
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return null;
	}

}
