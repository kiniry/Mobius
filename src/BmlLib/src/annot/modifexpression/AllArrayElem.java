package annot.modifexpression;

import annot.bcclass.BMLConfig;
 
/**
 * Deprecated - this expression when found ibn the specification will be  
 */
public class AllArrayElem  extends SpecArray {

	public static final AllArrayElem ALLARRAYELEM = new AllArrayElem();
	
	private AllArrayElem() {
	}

//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#setType()
//	 */
//	public void setType() {
//	}
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#getType()
//	 */
//	public Expression getType() {
//		// TODO Auto-generated method stub
//		return null;
//	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String printCode(BMLConfig conf) {
		return "*";
	}
}
