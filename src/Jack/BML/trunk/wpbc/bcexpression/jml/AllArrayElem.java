/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import java.util.Vector;

import type.BCType;
import bcexpression.Expression;
import bcexpression.WITH;
import bcexpression.javatype.JavaReferenceType;

import constants.BCConstantFieldRef;

/**
 * Deprecated - this expression when found ibn the specification will be  
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class AllArrayElem  extends JMLExpression {
	private Vector with;
	public AllArrayElem(Expression _left) {
		super(_left);
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
		// TODO Auto-generated method stub
		return null;
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		return this;
	}
}
