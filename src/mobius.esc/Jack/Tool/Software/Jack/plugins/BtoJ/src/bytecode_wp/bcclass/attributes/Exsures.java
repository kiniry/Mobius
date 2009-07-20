/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcclass.attributes;

import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.formula.Formula;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Exsures extends Postcondition {
	private JavaObjectType excType;
	
	
	public Exsures(Formula f, JavaObjectType _exc) {
		super(f);
		excType = _exc;
	}
	
	
	/**
	 * 
	 * @return Returns the excType after whic the formula must hold
	 */
	public JavaObjectType getExcType() {
		return excType;
	}
	/**
	 * @return
	 */
	public Formula getPredicate() {
		return getPostcondition();
	}



	
}
