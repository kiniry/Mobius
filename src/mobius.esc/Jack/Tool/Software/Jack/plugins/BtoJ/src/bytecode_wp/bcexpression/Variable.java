/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcexpression;

import bytecode_wp.bcexpression.jml.TYPEOF;

/**
 * @author mpavlova
 * 
 * This class represents a bound variable (used for quantified and unbound
 * variables)
 */
public class Variable extends Expression {
	private int id;

	private Expression type;

	

	/**
	 * constructor that considers that the default type of the variable is int
	 * 
	 * @param _id
	 */
	public Variable(int _id) {
		id = _id;
	}

	public Variable(int _id, Expression _type) {
		type = _type;
		id = _id;
	}


	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		/*if (type != null) {
			return type;
		}
		return new TYPEOF(this);*/
		return type;
	}

	public boolean equals(Expression e) {
		if (e == this) {
			return true;
		}
		if ( ! (e instanceof Variable)) {
			return false;
		}
		Variable v = (Variable ) e;
		if (( v.getId() == id) && (type == v.getType() ) ) {
			return true;
		}
		return false;
	}

	public Expression substitute(Expression _e1, Expression _e2) {
		return this;
	}


	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = "var(" + id + ")";
		return s;
	}


	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Variable copy = new Variable(id, type);
		return copy;
	}

	public int getId() {
		return id;
	}
}