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
 * @author io
 *
 * the class represents the JML constant elementype : array (JavaType) ---> JavaType 
 */
public class ELEMTYPE extends JMLExpression {

	
	private JML_CONST_TYPE type;
	
	public ELEMTYPE(Expression _left) {
		super(_left);
		setType();
	}

	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		type = new JML_CONST_TYPE();
	}
	
	public BCType getType() {
		return type;
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		
		return this;
	}
}
