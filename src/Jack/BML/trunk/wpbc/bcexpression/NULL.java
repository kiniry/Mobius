/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class NULL extends Expression {

	private static final NULL NULL = new NULL();
	private NULL() {}
	

	public static NULL getNULL() {
		return NULL;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return JavaType.JavaNULL;
	}
	public boolean equals(Expression _expr){ 
		if (_expr == this) {
			return true;
		}
		return false;
	}
	
	
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		return "NULL";
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy()  {
		return this;
	}
	
	
}
