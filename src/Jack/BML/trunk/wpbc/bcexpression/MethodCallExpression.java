/*
 * Created on Mar 3, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;


import type.BCType;
import constants.BCConstantMethodReference;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class MethodCallExpression extends  DOTExpression {
	private Expression[] args;
	
	public MethodCallExpression(BCConstantMethodReference _left, Expression _right , Expression[] _args ) {
		super(_left, _right);
		args = _args;
	} 
	public MethodCallExpression(Expression _left, Expression _right , Expression[] _args ) {
		super(_left, _right);
		args = _args;
	} 
	
	public Expression[] getArgs() {
		return args;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	
}
