package annot.bcexpression;

import annot.bcclass.BMLConfig;

//import bytecode_wp.bcexpression.javatype.JavaType;
//import annot.bcexpression.jml.OLD;
//import annot.bcexpression.jml.TYPEOF;
//import bytecode_wp.bcexpression.overload.FieldOverride;
//import annot.constants.BCConstantFieldRef;
//import annot.formula.Connector;
//import annot.formula.Formula;
//import annot.formula.Predicate0Ar;
//import annot.formula.Predicate2Ar;
//import annot.formula.PredicateSymbol;
//import annot.formula.Quantificator;
//import bytecode_wp.utils.FreshIntGenerator;

public class FieldAccess extends Expression {

	/**
	 * access to instance fields
	 * 
	 * @param _right
	 * @param _left
	 */
	public FieldAccess(Expression _constantFieldRef, Expression _obj_ref) {
		super(_constantFieldRef, _obj_ref);
		priority = 1;
	}

	/**
	 * access to static fields
	 * 
	 * @param _right
	 * @param _left
	 */
	public FieldAccess(Expression _constantFieldRef) {
		super(_constantFieldRef);
		priority = 1;
	}

//	/*
//	 * (non-Javadoc)
//	 * 
//	 * @see bcexpression.Expression#getType()
//	 */
//	public Expression getType() {
//		
//		if ((getFieldConstRef() instanceof BCConstantFieldRef)
//				|| (getFieldConstRef() instanceof OLD )
//				|| (getFieldConstRef() instanceof ValueAtState)) {
//			Expression type = getFieldConstRef().getType();
//			if (type == JavaType.JavaBOOLEAN) {
//				return JavaType.JavaINT;
//			}
//			return type;
//		}
//		return new TYPEOF(this);
//	}
//    
//    public Formula generateBoolExpressionConditions( ) {
//        Formula condition = Predicate0Ar.TRUE;
//        if ((getFieldConstRef() instanceof BCConstantFieldRef)
//                || (getFieldConstRef() instanceof OLD )
//                || (getFieldConstRef() instanceof ValueAtState)) {
//            Expression fRef = getFieldConstRef();
//            
//            if (fRef.isBooleanType()) {
//            	JavaType objType = (JavaType)getObject().getType();
//                /* 
//                 * if (getObject() != null) {
//            		objType =  (JavaType)getObject().getType();
//            	} else {
//            		objType = 
//            	} */
//                Variable o = new Variable(FreshIntGenerator.getInt(), objType  );
//                FieldAccess fAcc = new FieldAccess(getFieldConstRef(), o );
//                Predicate2Ar fAcc_eq_0 = new Predicate2Ar(fAcc, new NumberLiteral(0), PredicateSymbol.EQ ); 
//                Predicate2Ar fAcc_eq_1 = new Predicate2Ar(fAcc, new NumberLiteral(1), PredicateSymbol.EQ );
//                Formula f = Formula.getFormula(fAcc_eq_0, fAcc_eq_1, Connector.OR );
//                Quantificator q = new Quantificator(Quantificator.FORALL ,o );
//                condition = Formula.getFormula( f, q);
//            }
//        }
//        if (getObject() != null) {
//        	Formula f = getObject().generateBoolExpressionConditions();
//        	condition =(Formula) Formula.getFormula( condition , f, Connector.AND);
//        }
//        return condition ;    
//    }
//    
//    
//	public Expression getFieldConstRef() {
//		Expression constantFieldRef = getSubExpressions()[0];
//		return constantFieldRef;
//	}
//
//	public Expression getObject() {
//		if ( getSubExpressions().length < 2) {
//			return null;
//		}
//		return getSubExpressions()[1];
//	}
//
//	/*
//	 * (non-Javadoc)
//	 * 
//	 * @see bcexpression.Expression#equals(bcexpression.Expression)
//	 * 
//	 * public boolean equals(Expression _expr) { boolean equals =
//	 * super.equals(_expr); Expression constantFieldRef = getFieldConstRef(); if
//	 * (equals == true) { FieldAccess fAccess = (FieldAccess) _expr; Expression
//	 * _constantFieldRef = fAccess.getFieldConstRef(); equals = equals &&
//	 * (_constantFieldRef == constantFieldRef ? true : false); } return equals; }
//	 */
//
//	/**
//	 * the substitution is done if : the expression _e1 is a field access
//	 * expression and it accesses the same field as this object the type of the
//	 * object reference of this must be a subtype of the type of the object
//	 * reference of _e1
//	 * 
//	 * example : if a class A is declared / class A { public A X; } a = new A();
//	 * 
//	 * the expression : a.X.X[ ref.X <-- V] = a.X[ ref == a <-- V ].X[ ref ==
//	 * a.X[ ref == a <-- V ] <-- V ]
//	 */
//	public Expression substitute(Expression _e1, Expression _e2) {
//		Expression constantFieldRef = getFieldConstRef();
//		Expression obj = getObject();
//
//		if ( constantFieldRef instanceof ValueAtState) {
//			obj  = obj.substitute(_e1, _e2);
//			setSubExpressions(new Expression[]{ constantFieldRef, obj} );
//			return this;
//		}
//		if (this.equals(_e1)) {
//			return _e2.copy();
//		}
//		if ( ( (BCConstantFieldRef)constantFieldRef).isStatic()) {
//			if (this.equals(_e1)) {
//				return _e2.copy();
//			} else {
//				return this;
//			}
//		}
//		
//		// in the case this field is a static field
//		//if (getSubExpressions().length == 1) {
//		if (_e1 instanceof StaticFieldAccess) {
//			BCConstantFieldRef const_e1 = (BCConstantFieldRef) _e1
//					.getSubExpressions()[0];
//			if (const_e1.equals(constantFieldRef)) {
//				return _e2;
//			}
//			return this;
//		}
//		//}
//		
//		// in case _e1 is not an object of type FieldAccessExpression
//		if (!(_e1 instanceof FieldAccess)) {
//			constantFieldRef = constantFieldRef.substitute(_e1, _e2);
//			obj = obj.substitute(_e1, _e2);
//			setSubExpressions(new Expression[] { constantFieldRef, obj });
//			return this;
//		}
//		FieldAccess fieldAccess = (FieldAccess) _e1;
//		// in case _e1 is of type FieldAccessExpression but is not dereferncing
//		// the same field as this object
//		if (! fieldAccess.getFieldConstRef().equals( constantFieldRef)) {
//			constantFieldRef = constantFieldRef.substitute(_e1, _e2);
//			obj = obj.substitute(_e1, _e2);
//			setSubExpressions(new Expression[] { constantFieldRef, obj });
//			return this;
//		}
//		// in case _e1 is a reference to the same field
//		obj = obj.substitute(_e1, _e2);
//		FieldOverride with = new FieldOverride(constantFieldRef, obj, _e1
//				.getSubExpressions()[1].copy(), _e2.copy());
//		return with;
//	}

	public String printCode1(BMLConfig conf) {
		if (getSubExpressions().length == 1) {
			return getSubExpressions()[0].printCode(conf);
		} else {
			String str = getSubExpressions()[1].printCode(conf) + ".";
			if (str.contains("this"))
				str = "";
			return str + getSubExpressions()[0].printCode(conf);
		}
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {

		Expression[] copySubExpr = copySubExpressions();
		FieldAccess copy = null;
		if (copySubExpr.length == 2) {
			copy = new FieldAccess(copySubExpr[0], copySubExpr[1]);
		} else {
			copy = new FieldAccess(copySubExpr[0]);
		}
		return copy;
	}
}
