/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcexpression.ref;



import java.util.Vector;

import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaType;

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
		type = _type;
	}
	
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType()  {
		return type;
	}
	
	
	public boolean equals(Expression _expr) {
		boolean eq = super.equals(_expr);
		if (eq) {
			int refId  = ( (Reference)_expr).getId();
			if (refId == id) {
				return true;
			}
		}
		return false;
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
	
	
	
	/**
	 * @return Returns the id.
	 */
	public int getId() {
		return id;
	}
}
