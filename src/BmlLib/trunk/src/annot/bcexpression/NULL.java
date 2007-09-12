package annot.bcexpression;

import annot.bcclass.BMLConfig;

//import bytecode_wp.bcexpression.javatype.JavaType;

public class NULL extends Expression {

	private static final NULL NULL = new NULL();
	private NULL() {}

	public static NULL getNULL() {
		return NULL;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
//	public Expression getType() {
//		return JavaType.JavaNULL;
//	}
//	public boolean equals(Expression _expr){ 
//		if (_expr == this) {
//			return true;
//		}
//		return false;
//	}
//	
//	public Expression substitute(Expression _e1 , Expression _e2) { 
//		return this;
//	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String printCode1(BMLConfig conf) {
		return "NULL";
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy()  {
		return this;
	}
}
