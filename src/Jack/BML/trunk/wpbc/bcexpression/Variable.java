/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import type.BCType;
import bcexpression.javatype.JavaType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Variable extends Expression  {
	private int id;
	private JavaType type;
	
	public Variable(int _id) {
		id  = _id;
	}
	
	public Variable( int _id, JavaType _type) {
		type = _type;
		id = _id;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		return type;
	}
	
	public Expression substitute(Expression _e,  Expression _v) {
		if (equals( _e)) {
			return _v;
		}
		return null;
	}
	
}
