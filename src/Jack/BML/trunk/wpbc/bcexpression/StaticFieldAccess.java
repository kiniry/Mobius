/*
 * Created on Apr 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;
import java.util.Vector;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import type.BCType;
import constants.BCConstantClass;
import constants.BCConstantFieldRef;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class StaticFieldAccess extends Expression {
	private BCConstantFieldRef constantStaticFieldRef;
	//in case the static field is accessed directly from the class
	//the expression may represent either an object of type that has this
	// static
	//field either a java class
	private BCConstantClass clazz;
	private Vector with;
	public StaticFieldAccess(BCConstantFieldRef _constantFieldRef,
			BCConstantClass _clazz) {
		constantStaticFieldRef = _constantFieldRef;
		clazz = _clazz;
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
	/**
	 * @return
	 */
	public BCConstantFieldRef getConstantStaticFieldRef() {
		return constantStaticFieldRef;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#equals(bcexpression.Expression)
	 */
	public boolean equals(Expression _expr) {
		boolean equals = super.equals(_expr);
		if (equals == false) {
			return false;
		}
		StaticFieldAccess fAccess = (StaticFieldAccess) _expr;
		if (clazz != fAccess.getClazz()) {
			return false;
		}
		BCConstantFieldRef _constantFieldRef = fAccess
				.getConstantStaticFieldRef();
		equals = equals
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
		if (this.equals(_e1)) {
			return _e2;
		}
		if (_e1 instanceof StaticFieldAccess) {
			StaticFieldAccess sfa = (StaticFieldAccess) _e1;
			if (sfa.getConstantStaticFieldRef().equals(constantStaticFieldRef)) {
				JavaReferenceType _type_this = JavaType.getJavaRefType(clazz
						.getName());
				JavaReferenceType _type_e1 = JavaType.getJavaRefType(sfa
						.getClazz().getName());
				if (JavaType.subType(_type_this, _type_e1)) {
					return _e2;
				}
			}
		}
		return this;
	}
	/**
	 * @return Returns the clazz.
	 */
	public BCConstantClass getClazz() {
		return clazz;
	}
}