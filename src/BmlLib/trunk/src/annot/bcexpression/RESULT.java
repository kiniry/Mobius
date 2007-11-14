package annot.bcexpression;

import annot.bcclass.BCMethod;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

/**
 * This class represents <code>\result</code> expression
 * (return value of a method).
 * 
 * @author tomekb
 */
public class RESULT extends BCExpression {

	/**
	 * Method whose return value it represents.
	 */
	private BCMethod method;
	
	/**
	 * Return type of method <code>m</code>.
	 */
	private JavaType type;
	
	/**
	 * A standard constructor.
	 * 
	 * @param m - initializing method.
	 */
	public RESULT(BCMethod m) {
		super(Code.RESULT);
		this.method = m;
		this.type = JavaType.convert(
			m.getBcelMethod().getReturnType());
	}
	
	@Override
	protected JavaType checkType1() {
		return type;
	}

	@Override
	public JavaType getType1() {
		return type;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return IDisplayStyle._result;
	}

	@Override
	public String toString() {
		return IDisplayStyle._result;
	}

	/**
	 * @return method whose return value it represents.
	 */
	public BCMethod getMethod() {
		return method;
	}

}
