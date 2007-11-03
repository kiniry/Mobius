package annot.bcexpression;

import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents a shared object (bound or local
 * variable) reference.<br>
 * One instance per one occurence in expression.<br>
 * It's <code>sharedExpr</code> attribute can be the same (==)
 * in diffrent <code>SingleOccurence</code> expressions, eg.
 * Each reference to the same variable is diffrent expression,
 * but their's <code>sharedExpr</code> attribute is the same.
 * 
 * @author tomekb
 */
public class SingleOccurence extends BCExpression {

	/**
	 * Shared object (bound or local variable) this expression
	 * referes to.
	 */
	private BCExpression sharedExpr;

	/**
	 * A standard constructor.
	 * 
	 * @param expr - shared variable this expression
	 * 		refers to.
	 */
	public SingleOccurence(BCExpression expr) {
		super(Code.SINGLE_OCCURENCE);
		this.sharedExpr = expr;
	}

	@Override
	protected JavaType checkType1() {
		return sharedExpr.checkType1();
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType getType1() {
		return sharedExpr.getType();
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return sharedExpr.printCode1(conf);
	}

	@Override
	public String toString() {
		return sharedExpr.toString();
	}

	@Override
	public void write(AttributeWriter aw) {
		sharedExpr.write(aw);
	}

	/**
	 * @return shared object (bound or local variable)
	 * this expression referes to.
	 */
	public BCExpression getSharedExpr() {
		return sharedExpr;
	}

}
