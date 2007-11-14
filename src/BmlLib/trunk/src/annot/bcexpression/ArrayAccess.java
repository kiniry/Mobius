package annot.bcexpression;

import annot.bcexpression.javatype.JavaArrayType;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents array element reference.
 * 
 * @author tomekb
 */
public class ArrayAccess extends BCExpression {

	/**
	 * A standard constructor,
	 * for <code>array</code>[<code>index</code>] expression.
	 * 
	 * @param array - an expression representing an array
	 * 		variable.
	 * @param index - an expression representing index in
	 * 		<code>array</code>.
	 */
	public ArrayAccess(BCExpression array, BCExpression index) {
		super(Code.ARRAY_ACCESS, array, index);
	}

	public ArrayAccess(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected JavaType checkType1() {
		if (getSubExpr(1).getType() != JavaBasicType.JavaInt)
			return null;
		JavaType t = getSubExpr(0).getType();
		if (!(t instanceof JavaArrayType))
			return null;
		return ((JavaArrayType)t).getSingleType(); 
	}

	@Override
	public JavaType getType1() {
		return ((JavaArrayType)getSubExpr(0).getType()).getSingleType();
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printRawCode(conf)
			+ "[" + getSubExpr(1).printRawCode(conf) + "]";
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString()
			+ "[" + getSubExpr(1).toString() + "]";
	}

	@Override
	protected void read(AttributeReader ar, int root) throws ReadAttributeException {
		setSubExprCount(2);
		setSubExpr(0, ar.readExpression());
		setSubExpr(1, ar.readExpression());
	}

}
