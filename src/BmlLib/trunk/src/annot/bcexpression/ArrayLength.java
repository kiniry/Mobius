package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents ARRAYLENGTH constant. Eg. expression:
 * array.length
 * should have AST like:
 * FieldAccess(LocalVariable("array"), ARRAYLENGTH())
 * 
 * @author tomekb
 */
public class ArrayLength extends BCExpression {

	/**
	 * A standard constructor.
	 */
	public ArrayLength() {
		super(Code.ARRAYLENGTH);
	}

	@Override
	protected JavaType checkType1() {
		return JavaBasicType.JavaInt;
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType getType1() {
		return JavaBasicType.JavaInt;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return "length";
	}

	@Override
	public String toString() {
		return "array length";
	}

}
