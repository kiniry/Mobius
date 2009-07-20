/*
 * Created on Apr 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcexpression;

import bytecode_wp.bcexpression.javatype.JavaReferenceType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.constants.BCConstantClass;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class StaticFieldAccess extends FieldAccess {
	private BCConstantClass clazz;
	public StaticFieldAccess(Expression _constantFieldRef,
			BCConstantClass _clazz) {
		super(_constantFieldRef);
		clazz = _clazz;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 * 
	 * public Expression getType() {
	 * 
	 * return new TYPEOF(this); }
	 */
	/**
	 * @return
	 */
	public BCConstantFieldRef getConstantStaticFieldRef() {
		
		return (BCConstantFieldRef)getSubExpressions()[0];
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#equals(bcexpression.Expression)
	 */
	public boolean equals(Expression _expr) {
		Expression constantStaticFieldRef = getConstantStaticFieldRef();
		BCConstantClass clazz = getClazz();
		boolean equals = super.equals(_expr);
		if (equals == false) {
			return false;
		}
		StaticFieldAccess fAccess = (StaticFieldAccess) _expr;
		if (clazz != fAccess.getClazz()) {
			return false;
		}
		Expression _constantFieldRef = fAccess
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

		BCConstantFieldRef constantStaticFieldRef = (BCConstantFieldRef)getConstantStaticFieldRef();
		BCConstantClass clazz = getClazz();
		if (this.equals(_e1)) {
			return _e2.copy();
		}

		Expression constantStaticFieldRef_e1 = null;
		JavaReferenceType classWhereDecl = null; 
		if (_e1 instanceof StaticFieldAccess) {
			StaticFieldAccess sfa = (StaticFieldAccess) _e1;
			constantStaticFieldRef_e1 = sfa.getConstantStaticFieldRef();
			classWhereDecl = JavaType.getJavaRefType(sfa.getClazz().getName());
		}
		// in case the static field access is represented only by the constant 
		// field reference 
		if (_e1 instanceof BCConstantFieldRef) {
			constantStaticFieldRef_e1 = (BCConstantFieldRef)_e1;
			classWhereDecl = constantStaticFieldRef.getClassWhereDeclared();
		}
		if ((constantStaticFieldRef_e1 != null ) && (constantStaticFieldRef_e1.equals(constantStaticFieldRef))) {
			JavaReferenceType _type_this = JavaType.getJavaRefType(clazz
					.getName());
			if (JavaReferenceType.subType(_type_this, classWhereDecl)) {
				return _e2.copy();
			}
		}
		return this;
	}

	public BCConstantClass getClazz() {
		
		return clazz;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		BCConstantClass clazz = getClazz();
		String className = clazz.getName();
		String s = getSubExpressions()[0] + "";
		return s;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression constantStaticFieldRef = getConstantStaticFieldRef();
		BCConstantClass clazz = getClazz();
		StaticFieldAccess copy = new StaticFieldAccess(constantStaticFieldRef,
				clazz);
		return copy;
	}
    
    public Formula generateBoolExpressionConditions( ) {
        Formula condition = Predicate0Ar.TRUE;
        if ((getFieldConstRef() instanceof BCConstantFieldRef)
                || (getFieldConstRef() instanceof OLD )
                || (getFieldConstRef() instanceof ValueAtState)) {
            Expression type = getFieldConstRef().getType();
            if (getFieldConstRef().isBooleanType()) {
                Predicate2Ar fAcc_eq_0 = new Predicate2Ar(this, new NumberLiteral(0), PredicateSymbol.EQ ); 
                Predicate2Ar fAcc_eq_1 = new Predicate2Ar(this, new NumberLiteral(1), PredicateSymbol.EQ );
                condition = Formula.getFormula(fAcc_eq_0, fAcc_eq_1, Connector.OR );
            }
        }
        return condition ;
    }
	public Expression atState(int instrIndex, Expression expr) {
		if (getConstantStaticFieldRef().equals(expr) ) {
			return new ValueAtState( expr ,instrIndex);
		}
		return this;
	}
}