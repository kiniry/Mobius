package annot.modifexpression;
 
import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;

/**
 * @author mpavlova
 *
 * this class stands for the jml keyword everything used in the clause modifies in the method specification.
 *  if a method is declared to modify everything it is considered  that every field of the class that it belongs to, every public field of any class
 * of the same package and 
 *
 */
public class Everything  extends ModifiesExpression {
	
/*	public static Everything EVERYTHING = new  Everything(); */

	public Everything( ) {
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		return "\\everything";
	}

	public String printCode(BMLConfig conf) {
		return "\\everything";
	}

	//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#copy()
//	 */
//	public Expression copy() {
//		return EVERYTHING;
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
//
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#getType()
//	 */
//	public Expression getType() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return this;
	}
	
//	//////////////////////
//	////////////////////////////////////////////
//	/////////////////////////////////////////////////
//	/* (non-Javadoc)
//	 * @see modifexpression.ModifiesExpression#getCondition()
//	 */
//	public Expression getCondition() {
//		// TODO Auto-generated method stub
//		return this;
//	}
//
//
//	/* (non-Javadoc)
//	 * @see modifexpression.ModifiesExpression#getModifiedExpression()
//	 */
//	public Expression getExpression() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//
//	/* (non-Javadoc)
//	 * @see modifexpression.ModifiesExpression#getPostCondition()
//	 */
//	public Expression getPostCondition(IJml2bConfiguration config, int state) {
//		// TODO Auto-generated method stub
//		return Predicate0Ar.TRUE;
//	}
}
