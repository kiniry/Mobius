/*
 * Created on 14 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcexpression.jml.TYPEOF;


/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class LocalVariable extends Expression  {
	private int localVariableIndex;
	//private int local_index;
	
//	private Vector with;
	

	public LocalVariable(int _index_of_localVariable) {
		localVariableIndex = _index_of_localVariable;
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
	public Expression getType() {
		return new TYPEOF(this);
	}
	
	public boolean equals(Expression _expr) { 
		boolean equals = super.equals( _expr);
		if (equals == true) {
			LocalVariable lva = (LocalVariable)_expr;
			equals = equals && (lva.getIndex() == getIndex() ? true : false); 
		}
		return equals;
	}
	
	/**
	 * if this == _e1 then  _e2   else this
	 */ 
	public Expression substitute(Expression _e1 , Expression _e2) {
			if (this.equals( _e1)) {
				return _e2.copy();
			}
			return this;
	}
	
	/**
	 * @return Returns the index_of_localVariable.
	 */
	public int getIndex() {
		return localVariableIndex;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = "local(" +  localVariableIndex + ")";
		return s;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	 /**
	  * an instance of a local variable cannot be copied. teh methopd    
	  * returns the same instance
	  */
	public Expression copy() {
		return this;
	}
}
