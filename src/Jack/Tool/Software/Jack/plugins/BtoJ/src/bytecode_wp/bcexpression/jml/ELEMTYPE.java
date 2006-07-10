/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcexpression.jml;

import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaArrType;
import bytecode_wp.bcexpression.overload.FunctionOverload;
import bytecode_wp.bcexpression.overload.RefFunction;
import bytecode_wp.bcexpression.ref.ArrayReference;


/**
 * @author mpavlova
 *
 * the class represents the JML constant elementype : array (JavaType) ---> JML_CONST_Type 
 */
public class ELEMTYPE extends JMLExpression implements RefFunction{

	
	//private JML_CONST_TYPE type;
	
	public ELEMTYPE(Expression _subExpr) {
		super(_subExpr);
	}
	
	public Expression getType() {
		return JML_CONST_TYPE.JML_CONST_TYPE;
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		Expression subExpr = getSubExpressions()[0];
		subExpr = subExpr.substitute( _e1, _e2);
		if (_e2 instanceof ArrayReference) {
			FunctionOverload fApp  = new FunctionOverload(this, _e2.copy(),  (JavaArrType)_e2.getType());
			return fApp;
		}
		//setSubExpressions( new Expression[]{subExpr});
		return this;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		Expression expr = getSubExpressions()[0];
		String s = "elemType("   +expr.toString() + ")";
		return s;
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] copySubExpressions = copySubExpressions();
		ELEMTYPE copy = new ELEMTYPE(copySubExpressions[0]);
		return copy;
	}
}
