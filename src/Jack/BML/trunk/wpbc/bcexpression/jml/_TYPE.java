/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import bcexpression.Expression;
import bcexpression.javatype.JavaType;
import type.BCType;


/**
 * @author io
 *
 * this class represents the JML constant type : 
 */
public class _TYPE extends JMLExpression  {
	private JML_CONST_TYPE type;
	
	//jml expression : type( expression) where expression is a java type 
	public _TYPE(JavaType _type) {
		super(_type);
		setType();
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		type = new JML_CONST_TYPE();
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		if (type == null) {
			setType();
		}
		return type;
	} 
	
	public   boolean equals(Expression _expr){ 
		if ( _expr == this) {
			return true;
		}
		return false;
		
	}
	public Expression substitute(Expression _e1 , Expression _e2) { 
		return this;
	}
}
