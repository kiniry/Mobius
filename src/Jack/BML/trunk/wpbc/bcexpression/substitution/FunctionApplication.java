package bcexpression.substitution;

import utils.Util;
import bcexpression.ArrayAccessExpression;
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
	
	private RefFunction function;
	/*private Expression argument;*/
	private SubstitutionTree map;

	
	public FunctionApplication(RefFunction _function, Expression _arg,Expression _value  ) {
		function = _function;
		map = new SubstitutionTree( _arg, _value);
	}
	
	public FunctionApplication(RefFunction _function, SubstitutionTree _map) {
		function = _function;
		map = _map;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if ( function instanceof TYPEOF) {
			return substituteTypeOf(_e1, _e2);
		}
		if (function instanceof ELEMTYPE) {
			return substituteElemType(_e1, _e2);
		}
		if( function instanceof ArrayAccessExpression ) {
			return substituteArrayAtIndex(_e1, _e2);
		}
		return null;
	}

	/**
	 * @return
	 */
	private Expression substituteTypeOf(Expression _e1, Expression _e2) {
		TYPEOF expr = (TYPEOF)function;
		Expression subExpr = expr.getSubExpressions()[0];
		subExpr = subExpr.substitute(_e1, _e2);
		map = (SubstitutionTree)map.substitute(_e1, _e2);
		
		if ( _e2 instanceof Reference ) {
			JavaReferenceType refType = (JavaReferenceType)_e2.getType();
			map = new SubstitutionTree(map , new SubstitutionUnit(_e2, refType));
			return this;
		}
		/*TYPEOF typeof_expr = (TYPEOF)expr;*/
		Expression _expr = expr.getSubExpressions()[0];
		if(_expr instanceof JavaType) {
			return JML_CONST_TYPE.JML_CONST_TYPE;
		}
		Expression type = _expr.getType();
		
		if (type == null) {
			return this;
		}
		if (type instanceof JavaBasicType) {
			return (JavaBasicType)type;
		}
		
		return this;
	}
	
	private Expression substituteElemType(Expression _e1, Expression _e2) {
		ELEMTYPE expr = (ELEMTYPE)function;
		Expression subExpr = expr.getSubExpressions()[0];
		subExpr = subExpr.substitute(_e1, _e2);
		map = (SubstitutionTree)map.substitute(_e1, _e2);
		if (_e2 instanceof ArrayReference) {
			map = new SubstitutionTree(map, new SubstitutionUnit(_e2, (JavaArrType)_e2.getType()));
		}
		return this;
	}
	
	private Expression substituteArrayAtIndex(Expression _e1, Expression _e2) {
		ArrayAccessExpression arrayAccess = (ArrayAccessExpression)function;

		Expression array = arrayAccess.getArray();
		array = array.substitute(_e1, _e2);
		Expression index = arrayAccess.getIndex();
		index = index.substitute(_e1, _e2);
		arrayAccess.setSubExpressions(new Expression[]{array, index } );
		map = (SubstitutionTree)map.substitute(_e1, _e2);
		if (! (_e1 instanceof ArrayAccessExpression) ) {
			return this;
		}
		/*JavaType elemType = (JavaArrType)arrayAccess.getType() 
		ArrayAccessExpression e1AtIndex = (ArrayAccessExpression)_e1;
		Expression e1Array =  e1AtIndex.getArray();
		JavaType e1ElemType = e1AtIndex.getType(); 
		Expression e1Index =  e1AtIndex.getIndex();*/
		
		map = new SubstitutionTree(map, new SubstitutionUnit(_e1, _e2));
		
		return this;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return JML_CONST_TYPE.JML_CONST_TYPE;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		Expression _expr = ((Expression)function).getSubExpressions()[0]; 
		
		
		if (function instanceof TYPEOF) {
			String s = "[ typeof (" + map.toString() + ") " +_expr.toString() +" ]";
			return s;
		}
		if (function instanceof ELEMTYPE) {
			String s = "[ elemtype ( " + map.toString() + " ) " +_expr.toString() +" ]";
			return s;
		}
		if (function instanceof ArrayAccessExpression ) {
			ArrayAccessExpression arrayAtIndex = (ArrayAccessExpression)function; 
			Expression index = arrayAtIndex.getIndex();
			Expression array = arrayAtIndex.getArray();
			String s = "[ arrayAccess ( " + map.toString() + " ) (arr: " + array + " , ind: " + index + ")"; 
			return s;
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression fCopy = ((Expression)function).copy();
		SubstitutionTree mapCopy = (SubstitutionTree)map.copy();
		FunctionApplication thisCopy = new FunctionApplication((RefFunction)fCopy, mapCopy);
		return thisCopy;
	}

	public RefFunction getFunction() {
		return function;
	}
	public SubstitutionTree getMap() {
		return map;
	}
}
