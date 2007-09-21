package annot.attributes;

import annot.bcclass.BCMethod;
import annot.formula.AbstractFormula;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

/**
 * This class represents single specification case
 * of method specification.
 * 
 * @author tomekb
 */
public class SpecificationCase {

	/**
	 * A method this specificationCase specifies.
	 */
	private BCMethod method;

	/**
	 * This case should be considered only if its precondition
	 * evaluates to true.
	 */
	private AbstractFormula precondition;

	/**
	 * A condition that should be true if precondition is so.
	 */
	private AbstractFormula postcondition;

	/**
	 * Creates an empty specification case, with both
	 * precondition and postcondition set to true.
	 * 
	 * @param m - a method this specificationCase specifies.
	 */
	public SpecificationCase(BCMethod m) {
		this.method = m;
		this.precondition = Predicate0Ar.TRUE;
		this.postcondition = Predicate0Ar.TRUE;
	}

	/**
	 * A standard constructor.
	 * 
	 * @param m - a method this specificationCase specifies.
	 * @param precondition - specification case's precondition,
	 * @param postcondition - specification case's
	 * 		postcondition.
	 */
	public SpecificationCase(BCMethod m, AbstractFormula precondition,
			AbstractFormula postcondition) {
		this.method = m;
		this.precondition = precondition;
		this.postcondition = postcondition;
	}

	/**
	 * A constructor from AttributeReader, used only for
	 * loading specification case from .class file.
	 * 
	 * @param m - method this annotation specifies.
	 * @param ar - stream to load from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		specification case.
	 */
	public SpecificationCase(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		this(m);
		this.precondition = (AbstractFormula) ar.readExpression();
		this.postcondition = (AbstractFormula) ar.readExpression();
	}

	/**
	 * Saves specification case using AttributeWriter.
	 * 
	 * @param aw - stream to save to.
	 */
	public void write(AttributeWriter aw) {
		precondition.write(aw);
		postcondition.write(aw);
	}

	/**
	 * Prints specification case to a string.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return string representation of specificatoin case.
	 */
	public String printCode(BMLConfig conf) {
		String code = "";
		code += IDisplayStyle._sc_start + conf.newLine();
		conf.incInd();
		code += precondition.printLine(conf, IDisplayStyle._precondition);
		code += postcondition.printLine(conf, IDisplayStyle._postcondition);
		conf.decInd();
		code += IDisplayStyle._sc_end + conf.newLine();
		return code;
	}

}
