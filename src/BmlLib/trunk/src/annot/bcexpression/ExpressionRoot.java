package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

public class ExpressionRoot<T extends BCExpression> extends BCExpression {

	public ExpressionRoot(T subExpression) {
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
	public JavaType1 getType() {
		return getSubExpr(0).getType();
	}

	@Override
	protected void init() {}

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

}
