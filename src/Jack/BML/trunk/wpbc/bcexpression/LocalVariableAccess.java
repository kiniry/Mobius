/*
 * Created on 14 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import java.util.Vector;

import type.BCType;

import bcexpression.javatype.JavaType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class LocalVariableAccess extends Expression  {
	private int index_of_localVariable;
	//private int local_index;
	
	private Vector with;
	

	public LocalVariableAccess(int _index_of_localVariable) {
		index_of_localVariable = _index_of_localVariable;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
	
	public boolean equals(Expression _expr) { 
		boolean equals = super.equals( _expr);
		if (equals == true) {
			LocalVariableAccess lva = (LocalVariableAccess)_expr;
			equals = equals && (lva.getIndex() == getIndex() ? true : false); 
		}
		return equals;
	}
	
	/**
	 * if this == _e1 ==> this[ this<-- _e2] 
	 *    else this
	 */ 
	public Expression substitute(Expression _e1 , Expression _e2) {
		if (this.equals( _e1)) {
			return _e2;
		}
		if ( JavaType.subType((JavaType) _e1.getType(),(JavaType)getType() )) {
			WITH with = new WITH( _e1, _e2);
		}
		return this;
	}
	/**
	 * @return Returns the index_of_localVariable.
	 */
	public int getIndex() {
		return index_of_localVariable;
	}
}
