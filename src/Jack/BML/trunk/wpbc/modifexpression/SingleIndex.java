/*
 * Created on Sep 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class SingleIndex extends SpecArray {

	public SingleIndex(Expression index ) {
		super(index);
	}
	
	public Expression getIndex() {
		return getSubExpressions()[0];
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
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return null;
	}

}
