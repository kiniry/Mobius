/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import type.BCType;
import bcexpression.Expression;


/**
 * @author mpavlova
 *
 * the class represents the JML constant elementype : array (JavaType) ---> JML_CONST_Type 
 */
public class ELEMTYPE extends JMLExpression {

	
	private JML_CONST_TYPE type;
	
	public ELEMTYPE(Expression _subExpr) {
		super(_subExpr);
		setType();
	}

	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		type = JML_CONST_TYPE.JML_CONST_TYPE;
	}
	
	public BCType getType() {
		return type;
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		Expression subExpr = getSubExpressions()[0];
		subExpr = subExpr.substitute( _e1, _e2);
		//setSubExpressions( new Expression[]{subExpr});
		return this;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		Expression expr = getSubExpressions()[0];
		String s = "elemType("   +expr.toString() + ")";
		return s;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] copySubExpressions = copySubExpressions();
		ELEMTYPE copy = new ELEMTYPE(copySubExpressions[0]);
		return copy;
	}
}
