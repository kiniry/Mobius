/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.substitution;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class SubstitutionUnit  implements Tree {
	private  Expression  object;
	private  Expression  value;
	
	/**
	 * if the concrete object O in the field access is  equals to  _object then the field accessed has value  _value
	 * @param _object
	 * @param _value
	 */
	public SubstitutionUnit( Expression _object, Expression _value) {
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
	public Tree substitute(Expression e1, Expression e2)  {
//		Util.dump("SubstitutionUnit.substitute ****************** " + toString() + "[" +e1 + "<--"+ e2 + "]");
//		Util.dump("SubstitutionUnit  object before " + object.toString() );
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
	public Tree copy() {
		Expression objectCopy = object.copy();
		Expression valueCopy = value.copy();
		SubstitutionUnit unitCopy = new SubstitutionUnit( objectCopy, valueCopy) ;
		return unitCopy;
	}
	
}
