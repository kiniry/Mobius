package annot.bcexpression;

import annot.bcclass.BMLConfig;

/**
 * @author mpavlova
 * the class represents array access expression, i.e.  a[i]
 */
public class ArrayAccessExpression extends Expression {
	
	private boolean modifiedInLoop = false;
	
	/**
	 * @param _array the array object whose element at index _arrIndex is accessed 
	 * @param _arrIndex
	 */
	public ArrayAccessExpression(Expression  _array, Expression _arrIndex  ) {
		super(new Expression[]{_array, _arrIndex});
		priority = 1;
	}

//	public Expression loopModifArrayAtState(int instrIndex, Expression expr ) {
//		if ( expr.equals( getSubExpressions()[0]) ) {
//			modifiedInLoop = true;
//		}
//		return this;
//	}
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
//	 */
//	public Expression substitute(Expression _e1, Expression _e2) {
//		Expression[] subExpr = getSubExpressions();
//		if (modifiedInLoop) {
//			for (int i = 0; i< subExpr.length; i++) {
//				subExpr[i] = subExpr[i].substitute( _e1, _e2);
//			}
//			return this;
//		}
//		if ( equals(_e1)) {
//			return _e2;
//		}
//		for (int i = 0; i< subExpr.length; i++) {
//			subExpr[i] = subExpr[i].substitute( _e1, _e2);
//		}
//		if ( getSubExpressions()[0] instanceof  OLD) {
//			return this;
//		}
//		if (! ( _e1 instanceof ArrayAccessExpression) ) {
//			return this;
//		}
//		FunctionOverload with =  new FunctionOverload(this, _e1.copy(), _e2.copy() );
//		return with ;
//	}
//
//	public Expression getIndex() {
//		Expression index = getSubExpressions()[1];
//		return index;
//	}
//	
//	public Expression getArray() {
//		Expression array = getSubExpressions()[0];
//		return array;
//	}

	public String printCode1(BMLConfig conf) {
		String s ;
		Expression[] subExpr = getSubExpressions();
		s =  subExpr[0].printCode(conf) + "[" + subExpr[1].printCode(conf) + "]";
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] copySubExpr = copySubExpressions();
		ArrayAccessExpression copy = new ArrayAccessExpression(copySubExpr[0], copySubExpr[1] );
		return copy;
	}
}
