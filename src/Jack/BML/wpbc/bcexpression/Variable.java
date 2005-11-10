/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcexpression.jml.TYPEOF;

/**
 * @author mpavlova
 *
 * This class represents a bound variable  (used for quantified and unbound variables)
 */
public class Variable extends Expression  {
	private int id;
	private Expression type;
	
	public static final Variable DummyVariable = new Variable( 0);
	
	/**
	 * constructor that considers that the default type of the variable is int 
	 * @param _id
	 */
	public Variable(int _id) {
		id  = _id;
	}
	
	public Variable( int _id, Expression _type) {
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
	public Expression getType() {
		if (type != null) {
			return type;
		}
		return new TYPEOF(this);
	}


	public Expression substitute(Expression _e1,  Expression _e2) {
//			if (this.equals( _e1)) {
//				return _e2;
//			}
			return this;
	}
	
	
//	old version substitution	
//	public Expression substitute(Expression _e1,  Expression _e2) {
//		if (this.equals( _e1)) {
//			return _e2;
//		}
//		if (    (this.getType() instanceof JavaReferenceType) &&
//				(  _e1.getType() instanceof JavaReferenceType ) && 
//				(JavaType.subType((JavaReferenceType)getType(), (JavaReferenceType)_e1.getType() ) ) ) {
//			if(with == null) {
//				with = new Vector();
//			}
//			with.add(new EqualsObjects( _e1, _e2 )); 
//			
//		}
//		return this;
//	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = "var(" + id + ")";
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Variable copy = new Variable(id, type) ;
		return copy;
	}
		
	public int getId() {
		return id;
	}
}
