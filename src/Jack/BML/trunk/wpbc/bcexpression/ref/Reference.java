/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.ref;



import java.util.Vector;

import type.BCType;
import bcexpression.Expression;
import bcexpression.javatype.JavaType;

/**
 * @author io
 *
 */
public class Reference extends Expression {
	
	private JavaType type;
	private int id;
	
	private Vector with;
	
	public Reference(int _id, JavaType _type) {
		id = _id;
		setType(_type);
	}
	
	private void setType(JavaType _type) {
		type = _type;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType()  {
		return type;
	}
	/**
	 * 
	 * references are constants so substitution over a reference results in the same reference
	 * ref [ x<-- v ] = ref
	 * @return this object without changing it
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = "ref(" + id  + ")"; 
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		
		return this;
	}
	
	
	
}
