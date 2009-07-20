/*
 * Created on 17 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcexpression;


import bytecode_wp.bcexpression.javatype.JavaType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
/*
 * 
 * any instance of the class represents an instance of exception 
 * in the exptional postcondition 
 */
public class EXCEPTIONVariable extends Variable {
	

	/**
	 * @param _name
	 */
	public EXCEPTIONVariable(  int id, JavaType _exc_type) {
		super( id, _exc_type);
	}
}
