package bcexpression.substitution;

import type.BCType;
import bcexpression.Expression;
import bcexpression.javatype.JavaArrType;
import bcexpression.javatype.JavaBasicType;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.ELEMTYPE;
import bcexpression.jml.JML_CONST_TYPE;
import bcexpression.jml.TYPEOF;
import bcexpression.ref.ArrayReference;
import bcexpression.ref.Reference;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class FunctionApplication extends Expression {
	
	private Expression expr;
	private SubstitutionTree map;

	
	public FunctionApplication(Expression _expr, Expression _arg,Expression _value  ) {
		expr = _expr;
		map = new SubstitutionTree( _arg, _value);
	}
	
	public FunctionApplication(Expression _expr, SubstitutionTree _map) {
		expr = _expr;
		map = _map;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if ( expr instanceof TYPEOF) {
			return substituteTypeOf(_e1, _e2);
		}
		if (expr instanceof ELEMTYPE) {
			return substituteElemType(_e1, _e2);
		}
		return null;
	}

	/**
	 * @return
	 */
	private Expression substituteTypeOf(Expression _e1, Expression _e2) {
		Expression subExpr = expr.getSubExpressions()[0];
		subExpr = subExpr.substitute(_e1, _e2);
		map = (SubstitutionTree)map.substitute(_e1, _e2);
		
		if ( _e2 instanceof Reference ) {
			JavaReferenceType refType = (JavaReferenceType)_e2.getType();
			map = new SubstitutionTree(map , new SubstitutionUnit(_e2, refType));
			return this;
		}
		TYPEOF typeof_expr = (TYPEOF)expr;
		Expression _expr = expr.getSubExpressions()[0];
		if(_expr instanceof JavaType) {
			return JML_CONST_TYPE.JML_CONST_TYPE;
		}
		BCType type = _expr.getType();
		
		if (type == null) {
			return this;
		}
		if (type instanceof JavaBasicType) {
			return (JavaBasicType)type;
		}
		
		return this;
	}
	
	private Expression substituteElemType(Expression _e1, Expression _e2) {
		Expression subExpr = expr.getSubExpressions()[0];
		subExpr = subExpr.substitute(_e1, _e2);
		map = (SubstitutionTree)map.substitute(_e1, _e2);
		if (_e2 instanceof ArrayReference) {
			map = new SubstitutionTree(map, new SubstitutionUnit(_e2, (JavaArrType)_e2.getType()));
		}
		return this;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		return JML_CONST_TYPE.JML_CONST_TYPE;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		Expression _expr = expr.getSubExpressions()[0]; 
		if (expr instanceof TYPEOF) {
			String s = "[ typeof (" + map.toString() + ") " +_expr.toString() +" ]";
			return s;
		}
		if (expr instanceof ELEMTYPE) {
			String s = "[ elemtype ( " + map.toString() + " ) " +_expr.toString() +" ]";
			return s;
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression exprCopy = expr.copy();
		SubstitutionTree mapCopy = (SubstitutionTree)map.copy();
		FunctionApplication thisCopy = new FunctionApplication(exprCopy, mapCopy);
		return thisCopy;
	}

}
