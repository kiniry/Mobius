package annot.attributes;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.bcexpression.ExpressionRoot;
import annot.formula.AbstractFormula;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

/**
 * This class represents single assert annotation
 * (on or more InCodeAttribute per one bytecode instruction) 
 * 
 * @author tomekb
 */
public class SingleAssert extends InCodeAttribute {

	/**
	 * assert formula
	 */
	private ExpressionRoot<AbstractFormula> formula;

	/**
	 * Creates an empty annotation: '/assert true'.
	 * 
	 * @param m - BCMethod containing this annotation,
	 * @param ih - instructionHandle of bytecode instruction
	 * 		that this annotation should be attached to,
	 * @param minor - minor number of annotation, responsible
	 * 		for annotation ordering within single instruction.
	 */
	public SingleAssert(BCMethod m, InstructionHandle ih, int minor) {
		super(m, ih, minor);
		this.formula = new ExpressionRoot<AbstractFormula>(this, new Predicate0Ar(true));
	}

	/**
	 * A standard constructor.
	 * 
	 * @param m - BCMethod containing this annotation,
	 * @param ih - instructionHandle of bytecode instruction
	 * 		that this annotation should be attached to,
	 * @param minor - minor number of annotation, responsible
	 * 		for annotation ordering within single instruction.
	 */
	public SingleAssert(BCMethod m, InstructionHandle ih, int minor,
			AbstractFormula formula) {
		super(m, ih, minor);
		this.formula = new ExpressionRoot<AbstractFormula>(this, formula);
	}

	/**
	 * A constructor for tests only. It can be used only
	 * when we are sure that bytecode itself won't change.
	 * 
	 * @param m - BCMethod containing this annotation,
	 * @param pc - pc number of bytecode instruction that
	 * 		this annotation should be attached to. You should
	 * 		be sure that instruction of that pc really
	 * 		exists in given method.
	 * @param minor - minor number of annotation, responsible
	 * 		for annotation ordering within single instruction.
	 * @param f - assertion formula.
	 */
	@Deprecated
	public SingleAssert(BCMethod m, int pc, int minor, AbstractFormula f) {
		super(m, pc, minor);
		this.formula = new ExpressionRoot<AbstractFormula>(this, f);
	}

	/**
	 * A constructor for tests only. It can be used only
	 * when we are sure that bytecode itself won't change.
	 * Creates an empty assert (/assert true).
	 * 
	 * @param m - BCMethod containing this annotation,
	 * @param pc - pc number of bytecode instruction that
	 * 		this annotation should be attached to. You should
	 * 		be sure that instruction of that pc really
	 * 		exists in given method.
	 * @param minor - minor number of annotation, responsible
	 * 		for annotation ordering within single instruction.
	 */
	@Deprecated
	public SingleAssert(BCMethod m, int pc, int minor) {
		super(m, pc, minor);
		this.formula = new ExpressionRoot<AbstractFormula>(this, new Predicate0Ar(true));
	}

	/**
	 * Loads assertion content from AttributeReader.
	 * 
	 * @param ar - stream to load from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		assertion.
	 */
	@Override
	protected void load(AttributeReader ar) throws ReadAttributeException {
		formula = new ExpressionRoot<AbstractFormula>(this, ar.readFormula());
	}

	/**
	 * Saves assertion content using AttributeWriter.
	 * 
	 * @param aw - stream to save to.
	 */
	@Override
	protected void saveSingle(AttributeWriter aw) {
		formula.write(aw);
	}

	/**
	 * This method should simply print annotation to a string.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return string representation of assertion.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		return formula.printLine(conf, IDisplayStyle._assert);
	}

	/**
	 * @return annotation's type id, from AType interface.
	 */
	@Override
	protected int aType() {
		return AType.C_ASSERT;
	}

	/**
	 * @return Simple string represenatations of attribute,
	 * 		for use in debugger only.
	 */
	@Override
	public String toString() {
		return "assert at (" + getPC() + ", "
				+ ((getMinor() == -1) ? "any" : getMinor()) + ")";
	}

	/**
	 * @return assertion formula.
	 */
	public AbstractFormula getFormula() {
		return formula.getExpression();
	}

	@Override
	public ExpressionRoot[] getAllExpressions() {
		ExpressionRoot[] all = new ExpressionRoot[1];
		all[0] = formula;
		return all;
	}

}
