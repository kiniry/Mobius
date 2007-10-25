package annot.formula;

import annot.bcexpression.JavaBasicType;
import annot.bcexpression.JavaType1;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents 0Arg predicate, that is, TRUE
 * and FALSE predicates only. Each occurence of TRUE predicate
 * is represented by the same object (the same stands for
 * FALSE predicate).
 * 
 * @author tomekb
 */
public class Predicate0Ar extends AbstractFormula {

	/**
	 * A 'true' predicate.
	 */
	public static final Predicate0Ar TRUE = new Predicate0Ar(true);

	/**
	 * A 'false' predicate.
	 */
	public static final Predicate0Ar FALSE = new Predicate0Ar(false);

	/**
	 * Predicate value (true for 'true' predicate, and
	 * false for 'false' predicate).
	 */
	private boolean value;

	/**
	 * A private constructor
	 * 
	 * @param value - wether constructed object should be
	 * 		a 'true' predicate.
	 */
	private Predicate0Ar(boolean value) {
		this.value = value;
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
	 * Writes this predicate to AttributeWirter.
	 * 
	 * @param aw - stream to save to.
	 */
	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(value ? Code.TRUE : Code.FALSE);
	}

	/**
	 * Do not use this method.
	 * 
	 * @throws RuntimeException - always.
	 */
	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new RuntimeException("read() method unavaliable.");
	}

	/**
	 * Predicate 0Arg. has no subexpressions, so it has
	 * the highest priority.
	 * 
	 * @return priority of this expression
	 * 		(from annot.textio.Priorities).
	 */
	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	/**
	 * Does nothing.
	 */
	@Override
	protected void init() {
	}

	/**
	 * @return JavaType of this predicate, that is, JavaBool.
	 */
	@Override
	protected JavaType1 checkType1() {
		return JavaBasicType.JavaBool;
	}

}
