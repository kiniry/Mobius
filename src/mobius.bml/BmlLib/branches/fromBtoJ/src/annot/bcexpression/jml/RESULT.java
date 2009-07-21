package annot.bcexpression.jml;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;

public class RESULT extends JMLExpression {
	//private Vector with;

	private static RESULT result = new RESULT();

	private RESULT() {
	}
	
	public static RESULT getResult() {
		return result;
	}
	
//	/*
//	 * (non-Javadoc)
//	 * 
//	 * @see bcexpression.Expression#setType()
//	 */
//	public void setType() {
//		// TODO Auto-generated method stub
//	}
//	
//	/*
//	 * (non-Javadoc)
//	 * 
//	 * @see bcexpression.Expression#getType()
//	 */
//	public Expression getType() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//	public Expression substitute(Expression _e1, Expression _e2) {
//		if (this.equals(_e1)) {
//			return _e2.copy();
//		}
//		return this;
////		
////		if ((getType() instanceof JavaReferenceType)
////				&& (JavaType.subType((JavaType) this.getType(), (JavaType) _e1
////						.getType()))) {
////			if (with == null) {
////				with = new Vector();
////			}
////			with.add(new EqualsObjects(_e1, _e2));
////		}
////		return this;
//	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String printCode1(BMLConfig conf) {
		return "result";
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		return	this;
	}
}
