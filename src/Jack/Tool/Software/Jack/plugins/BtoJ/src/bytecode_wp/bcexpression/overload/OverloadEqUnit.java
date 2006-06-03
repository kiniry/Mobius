/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcexpression.overload;

import bytecode_wp.bcexpression.ArrayAccessExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.utils.Util;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class OverloadEqUnit extends OverloadUnit {

	/**
	 * if the concrete object O in the field access is  equals to  _object then the field accessed has value  _value
	 * @param _object
	 * @param _value
	 */
	public OverloadEqUnit( Expression _object, Expression _value) {
		super(_object, _value);
	}
	
	
	/**
	 * tests if the this overload unit overloads the expression <code> expr</code>.
	 * If it is the case then @return value
	 * else @return null
	 * @return
	 */
	/*protected Expression getExpressionOverloading( Expression expr) {
		if (expr == null) {
			Util.dump("Warning : OverloadUnit. getExpressionOverriden :  the argument cannot be null ");
			return null;
		}
		if (expr.equals( getObject()) ) {
			if (expr instanceof ArrayAccessExpression){
					Logger.get().println("coucou");
			}
			return getValue();
		}
		return null;
	}*/

	protected OverloadUnit getExpressionOverloading( Expression expr) {
		if (expr == null) {
			Util.dump("Warning : OverloadUnit. getExpressionOverriden :  the argument cannot be null ");
			return null;
		}
		if (expr.equals( getObject()) ) {
		/*	if (expr instanceof ArrayAccessExpression){
					Logger.get().println("coucou");
			}*/
			return this;
		}
		return null;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.substitution.Tree#copy()
	 */
	public Expression copy() {
		Expression objectCopy = getObject().copy();
		Expression valueCopy = getValue().copy();
		OverloadEqUnit unitCopy = new OverloadEqUnit( objectCopy, valueCopy) ;
		return unitCopy;
	}
	
	
}
