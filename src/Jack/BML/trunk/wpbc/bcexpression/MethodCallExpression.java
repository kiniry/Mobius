/*
 * Created on Mar 3, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;


import constants.BCConstantMethodReference;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class MethodCallExpression extends  CPExpression {
	private ExpressionList args;
	
	public MethodCallExpression(BCConstantMethodReference _left, Expression _right , ExpressionList _args ) {
		super(_left, _right);
		args = _args;
	} 
	 

	
}
