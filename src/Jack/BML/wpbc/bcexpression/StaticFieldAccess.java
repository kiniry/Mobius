/*
 * Created on Apr 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.TYPEOF;

import constants.BCConstantClass;
import constants.BCConstantFieldRef;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class StaticFieldAccess extends FieldAccess {
	

	public StaticFieldAccess(
		Expression _constantFieldRef,
		BCConstantClass _clazz) {
		super( _constantFieldRef, _clazz);
		
	}
/*	
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 
	public Expression getType() {

		return new TYPEOF(this);
	}*/
	/**
	 * @return
	 */
	public BCConstantFieldRef getConstantStaticFieldRef() {
		BCConstantFieldRef constantStaticFieldRef = (BCConstantFieldRef)getSubExpressions()[0];
		return constantStaticFieldRef;
	}
	

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#equals(bcexpression.Expression)
	 */
	public boolean equals(Expression _expr) {
		BCConstantFieldRef constantStaticFieldRef =  getConstantStaticFieldRef(); 
		BCConstantClass clazz = getClazz();
		boolean equals = super.equals(_expr);
		if (equals == false) {
			return false;
		}
		StaticFieldAccess fAccess = (StaticFieldAccess) _expr;
		if (clazz != fAccess.getClazz()) {
			return false;
		}
		BCConstantFieldRef _constantFieldRef =
			fAccess.getConstantStaticFieldRef();
		equals =
			equals
				&& (_constantFieldRef == constantStaticFieldRef ? true : false);
		return equals;
	}
	/**
	 * the substitution is done if : the expression _e1 is a field access
	 * expression and it accesses the same field as this object the type of the
	 * object reference of this must be a subtype of the type of the object
	 * reference of _e1
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		BCConstantFieldRef constantStaticFieldRef =  getConstantStaticFieldRef(); 
		BCConstantClass clazz = getClazz();
		if (this.equals(_e1)) {
			return _e2;
		}
		if (_e1 instanceof StaticFieldAccess) {
			StaticFieldAccess sfa = (StaticFieldAccess) _e1;
			if (sfa
				.getConstantStaticFieldRef()
				.equals(constantStaticFieldRef)) {
				JavaReferenceType _type_this =
					JavaType.getJavaRefType(clazz.getName());
				JavaReferenceType _type_e1 =
					JavaType.getJavaRefType(sfa.getClazz().getName());
				if (JavaType.subType(_type_this, _type_e1)) {
					return _e2;
				}
			}
		}
		return this;
	}
	public BCConstantClass getClazz() {
		BCConstantClass clazz = (BCConstantClass)getSubExpressions()[1];
		return clazz;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		BCConstantFieldRef constantStaticFieldRef =  getConstantStaticFieldRef(); 
		BCConstantClass clazz = getClazz();
		String s = "" + constantStaticFieldRef.getCPIndex();
		String className = clazz.getName();
		s = s + "(" + className + ")";
		return s;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		BCConstantFieldRef constantStaticFieldRef =  getConstantStaticFieldRef(); 
		BCConstantClass clazz = getClazz();
		StaticFieldAccess copy =
			new StaticFieldAccess(constantStaticFieldRef, clazz);
		return copy;
	}
}