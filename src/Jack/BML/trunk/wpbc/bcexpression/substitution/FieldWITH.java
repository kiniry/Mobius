/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.substitution;

import bcexpression.Expression;
import bcexpression.FieldAccess;
import constants.BCConstantFieldRef;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class FieldWITH extends Expression {
	// 
	private Expression constantFieldRef;
	private Expression object;
	private SubstitutionTree with;

	/**
	 * constructs a with expression where :
	 * @param _constantFieldRef is the index in the constant pool of the field reference 
	 * @param concreteObject  is the object that is dereferenced to obtain this object
	 * @param objWith - is the object that in case concreteObject is equal to the constantFieldRef(concreteObject) expression must be substituted with
	 * substituteExpression
	 * @param substituteWIth  - see the explanation for objWith
	 */
	public FieldWITH(
		Expression _constantFieldRef,
		Expression concreteObject,
		Expression objWith,
		Expression substituteWIth) {
		constantFieldRef = _constantFieldRef;
		object = concreteObject;
		with = new SubstitutionTree(objWith, substituteWIth);
	}
	
	private  FieldWITH(
	Expression _constantFieldRef,
	Expression concreteObject,
	SubstitutionTree _tree) {
		constantFieldRef = _constantFieldRef;
		object = concreteObject;
		with = _tree;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		object = object.substitute(_e1, _e2);
		with = (SubstitutionTree)with.substitute(_e1, _e2);
		constantFieldRef = constantFieldRef.substitute(_e1, _e2);
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
		with = new SubstitutionTree(with, new SubstitutionUnit(withObj, substituteWith));
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
	public SubstitutionTree getWith() {
		return with;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s =
			"["
				+ constantFieldRef.toString()
				+ " <+ "
				+ with.toString()
				+" (" +  object.toString() + ")  ]";
		return s;
	}

	/* (non-Javadoc)
		 * @see bcexpression.Expression#copy()
		 */
	public Expression copy() {
		Expression objectCopy = object.copy(); 
		SubstitutionTree withCopy  = (SubstitutionTree) with.copy();
		FieldWITH copy = new FieldWITH(constantFieldRef, objectCopy, withCopy );
		return copy;
	}
}
