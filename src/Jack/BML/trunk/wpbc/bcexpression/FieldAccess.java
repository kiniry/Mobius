/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;


import bcexpression.jml.TYPEOF;
import bcexpression.substitution.FieldWITH;

import utils.Util;
import constants.BCConstantFieldRef;
/**
 * @author io
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Generation - Code and Comments
 */
public class FieldAccess extends Expression {
	/*private BCConstantFieldRef constantFieldRef;
*/
	/**
	 * @param _right
	 * @param _left
	 */
	public FieldAccess(
		Expression _constantFieldRef,
		Expression _obj_ref) {
		super(_constantFieldRef, _obj_ref);
		/*constantFieldRef = _constantFieldRef;*/
	}
	
	/*
	 * (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return new TYPEOF(this );
	}
	public BCConstantFieldRef getFieldConstRef() {
		BCConstantFieldRef constantFieldRef = (BCConstantFieldRef)getSubExpressions()[0];
		return constantFieldRef;
	}
	public Expression getObject() {
		return getSubExpressions()[1];
	} 
	
	/*
	 * (non-Javadoc)
	 * @see bcexpression.Expression#equals(bcexpression.Expression)
	 */
	public boolean equals(Expression _expr) {
		boolean equals = super.equals(_expr);
		BCConstantFieldRef constantFieldRef =  getFieldConstRef();
		if (equals == true) {
			FieldAccess fAccess = (FieldAccess) _expr;
			BCConstantFieldRef _constantFieldRef = fAccess.getFieldConstRef();
			equals =
				equals
					&& (_constantFieldRef == constantFieldRef ? true : false);
		}
		return equals;
	}

	/**
	 * the substitution is done if : the expression _e1 is a field access
	 * expression and it accesses the same field as this object the type of the
	 * object reference of this must be a subtype of the type of the object
	 * reference of _e1
	 * 
	 * example : if a class A is declared / class A { public A X; } a = new
	 * A();
	 * 
	 * the expression : a.X.X[ ref.X <-- V] = 
	 * a.X[ ref == a <-- V ].X[ ref == a.X[ ref == a <-- V ] <-- V ]
	 */

	
	
	
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	*/
	public Expression substitute(Expression _e1, Expression _e2) {
		BCConstantFieldRef constantFieldRef =  getFieldConstRef();
//		Util.dump("***************************************************");
//		Util.dump("*****FieldAccessExpression.substitute : " + toString() + "[" + _e1.toString() + " <--- " + _e2.toString() + "]");
		if (this.equals(_e1)) {
			return _e2;
		}
		// the object whose field is dereferenced by this object 
		Expression obj = getSubExpressions()[1];
		// in case _e1 is not an object of type FieldAccessExpression
		if ( !( _e1 instanceof FieldAccess ) )  {
			obj = obj.substitute(_e1, _e2);
			setSubExpressions(new Expression[]{constantFieldRef, obj});
			return this;
		}
		FieldAccess fieldAccess = (FieldAccess)_e1;
		// in case _e1 is of type FieldAccessExpression but is not dereferncing the same field as this object
		if ( fieldAccess.getFieldConstRef().getCPIndex() != constantFieldRef.getCPIndex() ) {
			obj = obj.substitute(_e1, _e2);
			setSubExpressions(new Expression[]{constantFieldRef, obj});
			return this;
		}
		// in case _e1 is a reference to the same field
		obj = obj.substitute( _e1, _e2);
		FieldWITH with  = new FieldWITH(constantFieldRef,  obj, _e1.getSubExpressions()[1].copy(), _e2.copy()); 
		return with;
	}
	

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s =
			getSubExpressions()[0] + "(" + getSubExpressions()[1] + ")";
		return s;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] copySubExpr = copySubExpressions();
		FieldAccess copy = new FieldAccess((BCConstantFieldRef)copySubExpr[0] ,copySubExpr[1] );
		return copy;
	}

}
