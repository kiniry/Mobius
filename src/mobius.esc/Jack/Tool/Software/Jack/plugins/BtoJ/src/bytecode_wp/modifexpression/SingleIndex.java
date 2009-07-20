/*
 * Created on Sep 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.modifexpression;

import bytecode_wp.bcexpression.Expression;

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
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = "" + getSubExpressions()[0];   
		return s;
	}
	
}
