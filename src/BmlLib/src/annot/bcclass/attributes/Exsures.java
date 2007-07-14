package annot.bcclass.attributes;

import annot.bcclass.BMLConfig;
import annot.bcexpression.javatype.JavaObjectType;
import annot.formula.Formula;

public class Exsures extends Postcondition {
	private JavaObjectType excType;
	
	public Exsures(Formula f, JavaObjectType _exc) {
		super(f);
		excType = _exc;
	}
	
	public String printExsures(BMLConfig conf) {
		return excType.toString() + " " + printCode(conf);
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
