package bcexpression.jml;

import type.BCType;
import bcexpression.Expression;
import bcexpression.javatype.JavaBasicType;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.ref.Reference;
import bcexpression.substitution.FunctionApplication;
import bcexpression.substitution.SubstitutionTree;
import bcexpression.substitution.SubstitutionUnit;

/**
 * @author mpavlova
 *
 * the class represents the JML constant typeof : JavaType ---> JML_CONST_Type
 */
public class TYPEOF extends JMLExpression {
	private JML_CONST_TYPE type;
	public TYPEOF(Expression _expr) {
		super(_expr );
	}

	/* (non-Javadoc)
		 * @see bcexpression.Expression#setType()
		 */
		public void setType() {
			type = JML_CONST_TYPE.JML_CONST_TYPE;
		}
	
		public BCType getType() {
			return type;
		}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (equals(_e1)) {
			return _e2;
		}
 
		Expression[] subExpr = getSubExpressions();
		subExpr[0] = subExpr[0].substitute( _e1, _e2);
		BCType type = subExpr[0].getType();
//		if ( (_e1.getType() instanceof JavaReferenceType) && ( type instanceof JavaReferenceType) ) {
		if(_e2 instanceof Reference ) { 
			JavaReferenceType refType = (JavaReferenceType)_e2.getType();
			FunctionApplication fApp  = new FunctionApplication( this, _e2, refType);
			return fApp;
		}
		return this;
//		}
//		if ((_e1.getType() instanceof JavaBasicType) && ( type instanceof JavaBasicType)  ) {
//			JavaBasicType basicType = (JavaBasicType)_e2.getType();
//			FunctionApplication fApp  = new FunctionApplication(this , _e2, basicType);
//			return fApp;
//		}
//		return this;
	}
	
	/* (non-Javadoc)
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
