/*
 * Created on 17 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;


import bcexpression.type.*;

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
public class ExceptionVariable extends Variable {
	

	/**
	 * @param _name
	 */
	public ExceptionVariable( JavaType _exc_type, int id) {
		super(_exc_type, id);
	}
}
