package umbra.annot.bcclass.attributes;

import umbra.annot.bcexpression.javatype.JavaObjectType;
import umbra.annot.formula.Formula;

public class Exsures extends Postcondition {
	private JavaObjectType excType;
	
	public Exsures(Formula f, JavaObjectType _exc) {
		super(f);
		excType = _exc;
	}
	
//	/**
//	 * 
//	 * @return Returns the excType after whic the formula must hold
//	 */
//	public JavaObjectType getExcType() {
//		return excType;
//	}
//	/**
//	 * @return
//	 */
//	public Formula getPredicate() {
//		return getPostcondition();
//	}
}
