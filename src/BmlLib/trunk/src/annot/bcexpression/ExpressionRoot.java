package annot.bcexpression;

import annot.formula.AbstractFormula;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents a root of an expression.
 * Each attribute should have direct references ONLY to
 * expressions of this type, eg:<br>
 * <b>wrong:</b><br>
 * 		Assert.formula = Predicate2Ar(Code.LESS, expr1, expr2);
 * <br><b>correct:</b><br>
 * 		Assert.formula = ExpressinoRoot(Predicate2Ar(
 * 			Code.LESS, expr1, expr2));
 * 
 * @author tomekb
 * @param <T> - expected type of it's (only) subexpression;
 * 		eg. in Assert, use {@link AbstractFormula} as the
 * 		assert expression is always a formula.
 */
public class ExpressionRoot<T extends BCExpression> extends BCExpression {

	/**
	 * Parent attribute of this expression.
	 */
	private Object attribute;

	/**
	 * A standard constructor.
	 * 
	 * @param parent - use <b>this</b> as this parameter value,
	 * @param subExpression - the expression this class
	 * 		should represent.
	 */
	public ExpressionRoot(Object parent, T subExpression) {
		super(Code.EXPRESSION_ROOT);
		this.attribute = parent;
		this.setSubExprCount(1);
		this.setSubExpr(0, subExpression);
	}

	@Override
	protected JavaType1 checkType1() {
		return getSubExpr(0).checkType();
	}

	@Override
	protected int getPriority() {
		return Priorities.MAX_PRI;
	}

	@Override
	public JavaType1 getType1() {
		return getSubExpr(0).getType();
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		getSubExpr(0).read(ar, root);
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString();
	}

	@Override
	public void write(AttributeWriter aw) {
		getSubExpr(0).write(aw);
	}

	@SuppressWarnings("unchecked")
	public T getExpression() {
		return (T)getSubExpr(0);
	}

	/**
	 * Set it's (only) subexpression.
	 * 
	 * @param expr - new subexpression value.
	 */
	public void setExpression(T expr) {
		setSubExpr(0, expr);
	}

	/**
	 * @return a parent Object (it's creator, usually
	 * 		an attribute).
	 */
	public Object getAttribute() {
		return attribute;
	}

}
