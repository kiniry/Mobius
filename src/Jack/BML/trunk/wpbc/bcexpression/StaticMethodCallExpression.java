 /*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import type.BCType;
import constants.BCConstantClass;
import constants.BCConstantInterfaceMethodRef;
import constants.BCConstantMethodRef;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class StaticMethodCallExpression   extends Expression {

	
	private BCConstantMethodRef constantMethodReference;
	private BCConstantClass clazz;
	
	public StaticMethodCallExpression(BCConstantInterfaceMethodRef _const_ref, BCConstantClass _clazz, Expression[] _args ) {
		super(_args);
		constantMethodReference = _const_ref;
		clazz = _clazz;
		
	} 
	

	
	public Expression[] getArgs() {
		return getSubExpressions();
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
	/**
	 * @return
	 */
	public BCConstantMethodRef getConstantMethodReference() {
		return constantMethodReference;
	}

	/**
	 * @return the object class of 
	 */
	public BCConstantClass getClazz() {
		return clazz;
	}

	/**
	 * the method in the super class Expression checks if the subexpressions
	 * are equal. The subexpressions for a method call are the arguments passed
	 * to the method
	 */
	public boolean equals(Expression _expr) {
		boolean equals = super.equals(_expr);
		//the arguments are not the same
		if (equals == false) {
			return false;
		}
		StaticMethodCallExpression mCall = (StaticMethodCallExpression) _expr;
		BCConstantClass clazzOfmCall = mCall.getClazz();
		//the classes in the static method call expressions are not the same
		if (clazzOfmCall != clazz) {
			return false;
		}
		BCConstantMethodRef _constantMethodRef = mCall
				.getConstantMethodReference();
		equals = equals
				&& (_constantMethodRef == constantMethodReference
						? true
						: false);
		return equals;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		// TODO Auto-generated method stub
		return null;
	}

}
