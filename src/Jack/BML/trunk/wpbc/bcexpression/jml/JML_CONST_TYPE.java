/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import bcexpression.Expression;

/**
 * @author io
 *
 * this class represents the JML constant TYPE that is the type of all Java types
 *  */
public class JML_CONST_TYPE extends JMLExpression   {
	
	public static final  JML_CONST_TYPE JML_CONST_TYPE = new JML_CONST_TYPE();
	
	private JML_CONST_TYPE() {
		//setExpressionType(ExpressionConstants.TYPE);
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return this; //?may be this is a problem
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		return "TYPE";
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		return this;
	}
}
