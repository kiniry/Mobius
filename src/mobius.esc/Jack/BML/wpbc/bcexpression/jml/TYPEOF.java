package bcexpression.jml;

import bcexpression.Expression;
import bcexpression.NULL;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.overload.FunctionApplication;
import bcexpression.overload.RefFunction;
import bcexpression.ref.Reference;

/**
 * @author mpavlova
 * 
 * the class represents the JML constant typeof : JavaType ---> JML_CONST_Type
 */
public class TYPEOF extends JMLExpression implements RefFunction {

	public TYPEOF(Expression _expr) {
		super(_expr);
	}

	public Expression getType() {
		return JML_CONST_TYPE.JML_CONST_TYPE;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#substitute(bcexpression.Expression,
	 *      bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (equals(_e1)) {
			return _e2;
		}
		Expression[] subExpr = getSubExpressions();
		subExpr[0] = subExpr[0].substitute(_e1, _e2);
		Expression type = subExpr[0].getType();
		Expression expr = simplify();
		if (expr != this ) {
			return expr;
		}
		if (_e2 instanceof Reference) {
			JavaReferenceType refType = (JavaReferenceType) _e2.getType();
			FunctionApplication fApp = new FunctionApplication(this, _e2,
					refType);
			return fApp;
		}
		return this;
		//		}
		//		if ((_e1.getType() instanceof JavaBasicType) && ( type instanceof
		// JavaBasicType) ) {
		//			JavaBasicType basicType = (JavaBasicType)_e2.getType();
		//			FunctionApplication fApp = new FunctionApplication(this , _e2,
		// basicType);
		//			return fApp;
		//		}
		//		return this;
	}

	/**
	 * simplifies (evaluates  ) the expression. 
	 * If the this expression is of the form 
	 * typeof(ref) then @return ref.getType() 
	 * else if  typeof(NULL) @return the JavaType._Null type 
	 * else no simplifications are done and @return this 
	 */
	protected  Expression simplify() {

		Expression[] subExprs = getSubExpressions();
		Expression expr = subExprs[0];
		if (expr == NULL._NULL) {
			return JavaType._NULL;
		}
		if (expr instanceof Reference) {
			Reference ref = (Reference) expr;
			JavaType type = (JavaType) ref.getType();
			return type;
		}
		return this;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		Expression expr = getSubExpressions()[0];
		String s = "typeof(" + expr.toString() + ")";
		return s;
	}

	public Expression copy() {
		Expression[] copySubExpressions = copySubExpressions();
		TYPEOF copy = new TYPEOF(copySubExpressions[0]);
		return copy;
	}
}