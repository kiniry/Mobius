/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcexpression.type.JavaType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Variable extends Expression {
	
	private int id;
	private JavaType exc_type;
	public Variable() {
	}
	
	public Variable(JavaType _exc_type, int _id) {
		exc_type = _exc_type;
		id = _id;
	}
}
