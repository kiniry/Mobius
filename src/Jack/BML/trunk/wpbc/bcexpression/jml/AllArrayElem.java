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
 * Deprecated - this expression when found ibn the specification will be  
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class AllArrayElem  extends JMLExpression {

	public static final AllArrayElem ALLARRAYELEM = new AllArrayElem();
	
	
	private AllArrayElem() {
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		// TODO Auto-generated method stub
		return null;
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		return this;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		return "*";
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		return this;
	}
}
