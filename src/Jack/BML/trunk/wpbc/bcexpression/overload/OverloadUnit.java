/*
 * Created on Feb 2, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bcexpression.overload;

import utils.Util;
import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public abstract class OverloadUnit {
	private  Expression  object;
	private  Expression  value;
	
	/**
	 * if the concrete object O in the field access is  equals to  _object then the field accessed has value  _value
	 * @param _object
	 * @param _value
	 */
	public OverloadUnit( Expression _object, Expression _value) {
		object = _object;
		value = _value;
	}
	
	
	public Expression getObject( ) { 
		return object;
	}
	
	public Expression getValue( ) { 
			return value;
	}

	/* (non-Javadoc)
	 * @see bcexpression.objectsubstitution.Tree#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public OverloadUnit substitute(Expression e1, Expression e2)  {
//		if (e1.equals( object )) {
//			return value;
//		}		
		object = object.substitute(e1, e2.copy());
//		Util.dump("SubstitutionUnit  object after " + object.toString() );
//		Util.dump("SubstitutionUnit  value before " + value.toString() );
		value = value.substitute( e1, e2.copy());
//		Util.dump("SubstitutionUnit  value after " + value.toString() );
		return this;
	}
	
	public String toString() {
		// if the concrete object O in the field access is  equals to  "object" then the field accessed has value "value"
		String s = " (" + value.toString() + " <- " + object.toString() + ") ";
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.substitution.Tree#copy()
	 */
	public OverloadEqUnit copy() {
		Expression objectCopy = object.copy();
		Expression valueCopy = value.copy();
		OverloadEqUnit unitCopy = new OverloadEqUnit( objectCopy, valueCopy) ;
		return unitCopy;
	}
	
	/**
	 * tests if the this overload unit overloads the expression <code> expr</code>.
	 * If it is the case then @return value
	 * else @return null
	 * @return
	 */
	protected abstract Expression getExpressionOverloading( Expression expr);
}
