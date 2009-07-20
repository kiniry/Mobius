/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcexpression.overload;

import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.ValueAtState;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.constants.BCConstantFieldRef;

/**
 * @author mpavlova
 *
 * this class represents expressions whose interpretation
 * is a function application which is updated 
 */
public class FieldOverride extends Expression {
	
	private OverloadList overloads;

	/**
	 * constructs a with expression where :
	 * @param _constantFieldRef is the index in the constant pool of the field reference 
	 * @param concreteObject  is the object that is dereferenced to obtain this object
	 * @param objWith - is the object that in case concreteObject is equal to the constantFieldRef(concreteObject) expression must be substituted with
	 * substituteExpression
	 * @param substituteWIth  - see the explanation for objWith
	 */
	public FieldOverride(
		Expression _constantFieldRef,
		Expression concreteObject,
		Expression objWith,
		Expression substituteWIth) {
		super( _constantFieldRef, concreteObject);

		overloads = new OverloadList(objWith, substituteWIth);
	}
	
	private  FieldOverride(
	Expression _constantFieldRef,
	Expression concreteObject,
	OverloadList _tree) {
		super( _constantFieldRef, concreteObject);
		overloads = _tree;
	}
	
	

	public void setObject(Expression expr) {
		Expression[] subExp =  getSubExpressions();
		subExp[1] = expr;
	}
	
	public void setConstantField(Expression expr) {
		Expression[] subExp =  getSubExpressions();
		subExp[0] = expr;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		//Expression[] subExpr = getSubExpressions();
		setObject( getObject().substitute(_e1, _e2));
		setConstantField(getConstantFieldRef().substitute(_e1, _e2));
		overloads = (OverloadList)overloads.substitute(_e1, _e2);
		
		//////////////////////////////////
		///////////////substitution///////////////////
		// see if the there is an overloading for the value of the the object 
		
/*		Expression overloadingField = simplify();
		if (overloadingField != this) {
			return overloadingField;
		} */ 
			
		OverloadUnit overloadingField = overloads.getExpressionOverloading( getObject());
		if (overloadingField != null) {
			// if the object coincides with one of the overloadings return the overloading value 
			return overloadingField.getValue();
		}
	
		// if _e1 is not a field access expression  then return 
		if (!(_e1 instanceof FieldAccess)) {
			return this;
		}
		// if this is a field access expression but is not a field access to  to the same field as this fieldWITH expression
		if (getConstantFieldRef() != _e1.getSubExpressions()[0]) {
			return this;
		}
		// see if there is already an element that updates with the value of _e1
		Expression overloadingField1 =  overloads.getExpressionOverloading( _e1);
		if (overloadingField1 != null) {
			// if the object coincides with one of the overloadings return the overloading value 
			return overloadingField1;
		}
		
		// else if it is  field access expression to the same field as this fieldWITH then 
		// include it in the substitution tree
		Expression withObj = (((FieldAccess)_e1).getSubExpressions()[1]);
		Expression alreadyOverloadedForwithObj =  overloads.getExpressionOverloading( withObj);
		if (alreadyOverloadedForwithObj != null) {
			return this;
		}
		//make a copy of the object to evit substitution problems		
		overloads.overload(  new OverloadEqUnit(withObj.copy(), _e2.copy())); 
		return this;
	}
	
	/**
	 * simplifies the object if the concrete object coincides with one of the 
	 * updates
	 * @return eiither the simplified version of the object or the same object 
	 * if the object cannot be simplified
	 */
	public Expression simplify() {
		OverloadUnit overloadingField =  (OverloadUnit) overloads.getExpressionOverloading( getObject());
		if (overloadingField != null) {
			// if the object coincides with one of the overloadings return the overloading value 
			return overloadingField.getValue();
		}
		overloads.simplifyFieldUpdate();
		return this;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		if ((getConstantFieldRef() instanceof BCConstantFieldRef)
				|| (getConstantFieldRef() instanceof OLD )
				|| (getConstantFieldRef() instanceof ValueAtState)) {
			Expression type = getConstantFieldRef().getType();
			if (type == JavaType.JavaBOOLEAN) {
				return JavaType.JavaINT;
			}
			return type;
		}
		return null;
	}

	public Expression getConstantFieldRef() {
		return getSubExpressions()[0];
	}
	public Expression getObject() {
		return getSubExpressions()[1];
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
				+ getConstantFieldRef().toString()
				+" (" +  getObject().toString() + ")"
				+ " <+ "
				+ overloads.toString()
				+ "]";
		return s;
	}

	/* (non-Javadoc)
		 * @see bcexpression.Expression#copy()
		 */
	public Expression copy() {
		Expression objectCopy = getObject().copy(); 
		OverloadList withCopy  = (OverloadList) overloads.copy();
		FieldOverride copy = new FieldOverride(getConstantFieldRef(), objectCopy, withCopy );
		return copy;
	}
	
	public boolean equals(Expression expr) {
		boolean eq  = super.equals( expr);
		if (! eq ) {
			return false;
		}
		FieldOverride fo = (FieldOverride ) expr;
		OverloadList ol = fo.getWith();
		boolean eqOverloads = overloads.equals( ol);
		return eqOverloads;
	}
	
	
	public Expression atState(int instrIndex, Expression expr) {
		super.atState( instrIndex, expr);
		overloads = overloads.atState(instrIndex, expr);
		return this;
		
	}
}
