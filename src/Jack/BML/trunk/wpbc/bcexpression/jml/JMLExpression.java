/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import bcexpression.Expression;




/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class JMLExpression extends Expression {
	private Expression expr;

	protected JMLExpression() {
		
	}
	
	public JMLExpression(Expression _e, byte type) {	
		expr = _e;
		//setExpressionType(type);
	}
	
	
	public Object  getLeft() {
		return expr;
	}

	/**
	 * overriden fmethod from Expression. 
	 * As only one subexpresion is available there
	 * is no right subexpression
	 */
	public Object getRight() {
		return null;
	}
	
}
