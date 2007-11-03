package annot.bcexpression;

import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents <code>null</code> value.
 * 
 * @author tomekb
 */
public class NULL extends BCExpression {

	/**
	 * A standard constructor.
	 */
	public NULL() {
		super(Code.NULL);
	}
	
	@Override
	protected JavaType checkType1() {
		return JavaReferenceType.ANY;
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType getType1() {
		return JavaReferenceType.ANY;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return "null";
	}

	@Override
	public String toString() {
		return "null";
	}

}
