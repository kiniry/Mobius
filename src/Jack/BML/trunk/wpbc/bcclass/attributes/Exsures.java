/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcclass.attributes;

import formula.Formula;
import bcexpression.javatype.JavaObjectType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Exsures extends Specification {
	JavaObjectType excType;
	
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
}
