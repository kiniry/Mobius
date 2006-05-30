/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.modifexpression;

 
import bytecode_wp.bcexpression.Expression;


/**
 * Deprecated - this expression when found ibn the specification will be  
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class AllArrayElem  extends SpecArray {

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
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		return "*";
	}
}
