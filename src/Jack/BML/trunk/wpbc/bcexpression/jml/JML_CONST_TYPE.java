/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import type.BCType;

/**
 * @author io
 *
 * this class represents the JML constant TYPE that is the type of all Java types
 *  */
public class JML_CONST_TYPE extends JMLExpression implements BCType  {

	public JML_CONST_TYPE() {
		//setExpressionType(ExpressionConstants.TYPE);
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		return this; //?may be this is a problem
	}
}
