/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaArrType;
import bcexpression.overload.FunctionApplication;
import bcexpression.overload.RefFunction;
import bcexpression.vm.Stack;



/**
 * @author mpavlova
 * the class represents array access expression, i.e.  a[i]
 */
public class ArrayAccessExpression extends Expression implements RefFunction {
	
	
	
	/**
	 * @param _array the array object whose element at index _arrIndex is accessed 
	 * @param _arrIndex
	 */
	public ArrayAccessExpression(Expression  _array, Expression _arrIndex  ) {
		super(new Expression[]{_array, _arrIndex});
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if ( equals(_e1)) {
			return _e2;
		}
		Expression[] subExpr = getSubExpressions();
		
		for (int i = 0; i< subExpr.length; i++) {
			subExpr[i] = subExpr[i].substitute( _e1, _e2);
		}
		
		if (! ( _e1 instanceof ArrayAccessExpression) ) {
			return this;
		}
		ArrayAccessExpression _eArr  = (ArrayAccessExpression)_e1;
		
		FunctionApplication with =  new FunctionApplication(this, _e1.copy(), _e2.copy() );
		return with ;
	}

	public Expression getIndex() {
		Expression index = getSubExpressions()[1];
		return index;
	}
	public Expression getArray() {
		Expression array = getSubExpressions()[0];
		return array;
	}
	
	
	

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s ;
		Expression[] subExpr = getSubExpressions();
		s =  subExpr[0] + "[" + subExpr[1] + "]";
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
