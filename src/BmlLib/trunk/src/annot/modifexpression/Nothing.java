package annot.modifexpression;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;

public class Nothing extends ModifiesExpression {
	public static Nothing NOTHING = new Nothing();
	
	private Nothing() {}
	
	public String printCode(BMLConfig conf) {
		return "\\nothing";
	}

//	/* (non-Javadoc)
//	 * @see modifexpression.ModifiesExpression#getPostCondition()
//	 */
//	public Expression getPostCondition(IJml2bConfiguration config, int state) {
//		return Predicate0Ar.TRUE;
//	}
//
//	/* (non-Javadoc)
//	 * @see modifexpression.ModifiesExpression#getExpression()
//	 */
//	public Expression getExpression() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
//	 */
//	public Expression substitute(Expression _e1, Expression _e2) {
//		// TODO Auto-generated method stub
//		return this;
//	}
//
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#copy()
//	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return this;
	}


}
