package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents a conditionalExpression (?:).
 * 
 * @author tomekb
 */
public class ConditionalExpression extends AbstractIntExpression {

	/**
	 * A standard constructor.<br>
	 * <code>condition</code> ? <code>iftrue</code> : <br>
	 * <code>iffalse</code>
	 * 
	 * @param condition - a boolean expression,
	 * @param ifTrue - integer expression; value of this
	 * 		expression if <code>condition</code> evaluates
	 * 		to true,
	 * @param ifFalse - integer expression; value of this
	 * 		expression if <code>condition</code> evaluates
	 * 		to false.
	 */
	public ConditionalExpression(BCExpression condition, BCExpression ifTrue, BCExpression ifFalse) {
		super(Code.COND_EXPR);
		setSubExprCount(3);
		setSubExpr(0, condition);
		setSubExpr(1, ifTrue);
		setSubExpr(2, ifFalse);
	}

	/**
	 * A constructor from AttributeReader, used for loading
	 * from file (from BCEL's unknown Attribute).
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type o expression (last read byte from
	 * 		<code>ar</code>.
	 * @throws ReadAttributeException - if stream
	 * 		in <code>ar</code> doesn't represent a correct
	 * 		conditional expression.
	 * @see BCExpression#BCExpression(AttributeReader, int)
	 */
	public ConditionalExpression(AttributeReader ar, int root)
		throws ReadAttributeException {
			super(ar, root);
	}

	@Override
	protected int getPriority() {
		return Priorities.getPriority(Code.COND_EXPR);
	}

	@Override
	protected JavaType1 checkType1() {
		if ((getSubExpr(0).checkType() != JavaBasicType.JavaBool)
			|| (getSubExpr(1).checkType() != JavaBasicType.JavaInt)
			|| (getSubExpr(2).checkType() != JavaBasicType.JavaInt))
				return null;
		return JavaBasicType.JavaInt;
	}

	@Override
	protected void init() {}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf)
			+ " ? " + getSubExpr(1).printCode(conf)
			+ " : " + getSubExpr(2).printCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		BCExpression cond = ar.readExpression();
		BCExpression ifTrue = ar.readExpression();
		BCExpression ifFalse = ar.readExpression();
		setSubExprCount(3);
		setSubExpr(0, cond);
		setSubExpr(1, ifTrue);
		setSubExpr(2, ifFalse);
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString()
			+ " ? " + getSubExpr(1).toString()
			+ " : " + getSubExpr(2).toString();
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.COND_EXPR);
		getSubExpr(0).write(aw);
		getSubExpr(1).write(aw);
		getSubExpr(2).write(aw);
	}

}
