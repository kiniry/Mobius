/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import constants.BCConstantInterfaceMethodRef;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class StaticMethodCallExpression extends CPExpression {

	private ExpressionList args;

	public StaticMethodCallExpression(
		BCConstantInterfaceMethodRef _left,
		Expression _right,
		ExpressionList _args) {
		super(_left, _right);
		args = _args;
	}

	public ExpressionList getArgs() {
		return args;
	}

}
