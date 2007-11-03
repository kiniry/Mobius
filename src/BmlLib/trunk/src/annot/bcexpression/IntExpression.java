package annot.bcexpression;

import annot.io.AttributeWriter;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This ugly class converts an expression
 * to {@link AbstractIntExpression}.
 * 
 * @author tomekb
 * @see BooleanExpression
 */
public class IntExpression extends AbstractIntExpression {

	/**
	 * A standard constructor.
	 * 
	 * @param subExpr - expression it should represent.
	 * 		It should have a int return type, but
	 * 		it shouldn't be an AbstractIntExpression.
	 */
	public IntExpression(BCExpression subExpr) {
		super(-1, subExpr);
	}

	@Override
	protected JavaType1 checkType1() {
		JavaType1 type = getSubExpr(0).getType();
		if (type != JavaBasicType.JavaInt)
			return null;
		return JavaBasicType.JavaInt;
	}

	@Override
	protected int getPriority() {
		return Priorities.PRI_TRANSPARENT;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printRawCode(conf);
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString();
	}

	@Override
	public void write(AttributeWriter aw) {
		getSubExpr(0).write(aw);
	}

}
