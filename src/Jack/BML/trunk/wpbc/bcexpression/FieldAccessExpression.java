/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;
import java.util.Vector;
import bcexpression.javatype.JavaType;
import type.BCType;
import constants.BCConstantFieldRef;
/**
 * @author io
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Generation - Code and Comments
 */
public class FieldAccessExpression extends Expression {
	private BCConstantFieldRef constantFieldRef;
	//private Expression objectReference;
	private Vector with;
	/**
	 * @param _right
	 * @param _left
	 */
	public FieldAccessExpression(BCConstantFieldRef _constantFieldRef,
			Expression _obj_ref) {
		super(_obj_ref);
		constantFieldRef = _constantFieldRef;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
	public BCConstantFieldRef getFieldConstRef() {
		return constantFieldRef;
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#equals(bcexpression.Expression)
	 */
	public boolean equals(Expression _expr) {
		boolean equals = super.equals(_expr);
		if (equals == true) {
			FieldAccessExpression fAccess = (FieldAccessExpression) _expr;
			BCConstantFieldRef _constantFieldRef = fAccess.getFieldConstRef();
			equals = equals
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
	 * the expression : a.X.X[ ref.X <-- V] = a.X[ ref == a <-- V ].X[ref ==
	 * a.X[ ref == a <-- V ] <-- V ]
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (this.equals(_e1)) {
			return _e2;
		}
		Expression objRef = getSubExpressions()[0];
		if (_e1 instanceof FieldAccessExpression) {
			FieldAccessExpression fa = (FieldAccessExpression) _e1;
			Expression objRefOf_e1 = fa.getSubExpressions()[0];
			if ((fa.getFieldConstRef().equals(getFieldConstRef()))
					&& (JavaType.subType((JavaType) objRef.getType(),
							(JavaType) objRefOf_e1.getType()))) {
				if (with == null) {
					with = new Vector();
				}
				with.add(new WITH(objRefOf_e1, _e2));
			}
		}
		//try to do the substitution in the objectref expression
		//this substitution is valid basically for recursove data types
		objRef = objRef.substitute(_e1, _e2);
		return this;
	}

}
