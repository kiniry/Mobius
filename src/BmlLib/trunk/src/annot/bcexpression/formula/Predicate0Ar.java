package annot.bcexpression.formula;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.tmp.AbstractFormula;

/**
 * This class represents 0Arg predicate, that is, TRUE
 * and FALSE predicates only.
 * 
 * @author tomekb
 */
public class Predicate0Ar extends AbstractFormula {


	/**
	 * Predicate value (true for 'true' predicate, and
	 * false for 'false' predicate).
	 */
	private boolean value;

	/**
	 * A standard constructor.
	 * 
	 * @param value - whether constructed object should be
	 * 		a 'true' predicate.
	 */
	public Predicate0Ar(boolean value) {
		super(value ? Code.TRUE : Code.FALSE);
		this.value = value;
	}

	
	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param root - expression's connector (opcode).
	 */
	public Predicate0Ar(int root) {
		super(root);
		this.value = (root == Code.TRUE);
	}
	
	/**
	 * Prints expression to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of this predicate:
	 * 		"true" for TRUE, and "false" for FALSE.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		return "" + value;
	}

	/**
	 * @return Simple String representation of this
	 * 		predicate, for debugging only.
	 */
	@Override
	public String toString() {
		return "" + value;
	}

	/**
	 * @return JavaType of this predicate, that is, JavaBool.
	 */
	@Override
	protected JavaType checkType1() {
		return JavaBasicType.JavaBool;
	}

}
