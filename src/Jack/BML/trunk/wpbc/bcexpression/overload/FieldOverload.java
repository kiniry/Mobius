/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.overload;

import bcexpression.Expression;
import bcexpression.FieldAccess;
import constants.BCConstantFieldRef;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class FieldOverload extends Expression {
	// 
	private Expression constantFieldRef;
	private Expression object;
	private OverloadList overloads;

	/**
	 * constructs a with expression where :
	 * @param _constantFieldRef is the index in the constant pool of the field reference 
	 * @param concreteObject  is the object that is dereferenced to obtain this object
	 * @param objWith - is the object that in case concreteObject is equal to the constantFieldRef(concreteObject) expression must be substituted with
	 * substituteExpression
	 * @param substituteWIth  - see the explanation for objWith
	 */
	public FieldOverload(
		Expression _constantFieldRef,
		Expression concreteObject,
		Expression objWith,
		Expression substituteWIth) {
		constantFieldRef = _constantFieldRef;
		object = concreteObject;
		overloads = new OverloadList(objWith, substituteWIth);
	}
	
	private  FieldOverload(
	Expression _constantFieldRef,
	Expression concreteObject,
	OverloadList _tree) {
		constantFieldRef = _constantFieldRef;
		object = concreteObject;
		overloads = _tree;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		object = object.substitute(_e1, _e2);
		overloads = (OverloadList)overloads.substitute(_e1, _e2);
		constantFieldRef = constantFieldRef.substitute(_e1, _e2);
		
		//////////////////////////////////
		///////////////substitution///////////////////
		// see if the there is an overloading for the value of the the object 
		Expression overloadingField =  overloads.getExpressionOverloading( object);
		if (overloadingField != null) {
			// if the object coincides with one of the overloadings return the overloading value 
			return overloadingField;
		}
		
		
		// if _e1 is not a field access expression  then return 
		if (!(_e1 instanceof FieldAccess)) {
			return this;
		}
		// if this is a field access expression but is not a field access to  to the same field as this fieldWITH expression
		if (constantFieldRef != _e1.getSubExpressions()[0]) {
			return this;
		}
		
		// else if it is  field access expression to the same field as this fieldWITH then 
		// include it in the substitution tree
		Expression withObj = (((FieldAccess)_e1).getSubExpressions()[1]).copy();
		Expression substituteWith =  _e2.copy();
		overloads.overload(  new OverloadEqUnit(withObj, substituteWith)); //new Overload(with, new OverloadUnit(withObj, substituteWith));
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		// TODO Auto-generated method stub
		return null;
	}

	public Expression getConstantFieldRef() {
		return constantFieldRef;
	}
	public Expression getObject() {
		return object;
	}
	public OverloadList getWith() {
		return overloads;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s =
			"["
				+ constantFieldRef.toString()
				+ " <+ "
				+ overloads.toString()
				+" (" +  object.toString() + ")  ]";
		return s;
	}

	/* (non-Javadoc)
		 * @see bcexpression.Expression#copy()
		 */
	public Expression copy() {
		Expression objectCopy = object.copy(); 
		OverloadList withCopy  = (OverloadList) overloads.copy();
		FieldOverload copy = new FieldOverload(constantFieldRef, objectCopy, withCopy );
		return copy;
	}
}
