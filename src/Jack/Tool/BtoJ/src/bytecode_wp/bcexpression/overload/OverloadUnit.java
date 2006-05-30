/*
 * Created on Feb 2, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.bcexpression.overload;


import bytecode_wp.bcexpression.Expression;


/**
 * @author mpavlova
 */
public abstract class OverloadUnit extends Expression {
	private Expression object;

	private Expression value;

	/**
	 * if the concrete object O in the field access is equals to _object then
	 * the field accessed has value _value
	 * 
	 * @param _object
	 * @param _value
	 */
	public OverloadUnit(Expression _object, Expression _value) {
		
		object = _object;
		value = _value;
	}

	public Expression getObject() {
		return object;
	}

	public Expression getValue() {
		return value;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.objectsubstitution.Tree#substitute(bcexpression.Expression,
	 *      bcexpression.Expression)
	 */
	public Expression substitute(Expression e1, Expression e2) {
		// if (e1.equals( object )) {
		// return value;
		// }

		object = object.substitute(e1, e2.copy());
		// Util.dump("SubstitutionUnit object after " + object.toString() );
		// Util.dump("SubstitutionUnit value before " + value.toString() );
		value = value.substitute(e1, e2.copy());
		// Util.dump("SubstitutionUnit value after " + value.toString() );
		return this;
	}

	public String toString() {
		// if the concrete object O in the field access is equals to "object"
		// then the field accessed has value "value"
		String s = " ( WITH " + object.toString() + " <- " + value.toString()
				+ ") ";
		return s;
	}

	public boolean equals(Object obj) {
		if (obj.getClass() != getClass()) {
			return false;
		}
		boolean eq = value.equals(((OverloadUnit) obj).getValue());
		eq = eq && obj.equals(((OverloadUnit) obj).getObject());
		return eq;
	}

	public abstract Expression copy();

	/**
	 * 
	 * tests if the this overload unit overloads the expression
	 * <code> expr</code>. If it is the case then
	 * 
	 * @return value else
	 * @return null
	 * @return
	 */
	protected abstract OverloadUnit getExpressionOverloading(Expression expr);

	public Expression atState(int instrIndex, Expression expr) {
		object = object.atState(instrIndex, expr);
		value = value.atState(instrIndex, expr);
		return this;
	}

	public void setObject(Expression e) {
		object = e;
	} 
	
	public void seValue(Expression e) {
		value = e;
	}
	
/*	*//**
	 * simplifies the update data structure 
	 * called only for ArrayExpressions
	 *//*
	public Expression simplify() {
		if (getObject() instanceof FunctionApplication) {
			FunctionApplication fApp = (FunctionApplication) getObject();
			RefFunction exp = fApp.getFunction();
			if (exp instanceof ArrayAccessExpression) {
				OverloadList list = fApp.getMap();
				OverloadUnit overloading = list
						.getExpressionOverloading((ArrayAccessExpression) exp);
				if (overloading != null) {
					return new OverloadEqUnit((ArrayAccessExpression) exp,
							getValue());
				}
			}
		}
		return this;
	}*/
}
