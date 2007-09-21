package annot.attributes;

import org.antlr.runtime.RecognitionException;
import annot.bcclass.BCMethod;
import annot.formula.AbstractFormula;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Parsing;

/**
 * This class represents method specification attribute.
 * 
 * @author tomekb
 */
public class MethodSpecification extends BCPrintableAttribute implements
		IBCAttribute {

	/**
	 * Method this annotation specifies.
	 */
	private BCMethod method;

	/**
	 * This should be true before first method's instruction.
	 */
	private AbstractFormula precondition;

	/**
	 * Each of this cases specifies method's behaviour
	 * in some conditions (if their's precondition's are true).
	 */
	private SpecificationCase[] specCases;

	/**
	 * Creates an empty method specification,
	 * which tells nothing.
	 * 
	 * @param m - method this annotation specifies.
	 */
	public MethodSpecification(BCMethod m) {
		this(m, Predicate0Ar.TRUE, new SpecificationCase[0]);
	}

	/**
	 * A standard constructor.
	 * 
	 * @param m - method this annotation specifies,
	 * @param precondition - it's precondition,
	 * @param sc - and specification cases.
	 */
	public MethodSpecification(BCMethod m, AbstractFormula precondition,
			SpecificationCase[] sc) {
		this.method = m;
		this.precondition = precondition;
		this.specCases = sc;
	}

	/**
	 * A constructor from AttributeReader, used only for
	 * loading method specification from .class file.
	 * 
	 * @param m - method this annotation specifies.
	 * @param ar - stream to load from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		method specification.
	 */
	public MethodSpecification(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		this.method = m;
		this.precondition = (AbstractFormula) ar.readExpression();
		int length = ar.readAttributesCount();
		specCases = new SpecificationCase[length];
		for (int i = 0; i < length; i++)
			specCases[i] = new SpecificationCase(m, ar);
	}

	/**
	 * Prints annotation to a string.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return string representation of method specification.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		String code = precondition.printLine(conf, IDisplayStyle._requires);
		if (specCases.length > 0)
			for (int i = 0; i < specCases.length; i++)
				code += specCases[i].printCode(conf);
		return Parsing.addComment(code);
	}

	/**
	 * Replaces this annotation with a given one, updating
	 * nessesery references in BCMethod.
	 * 
	 * @param pa - annotation to replace with.
	 */
	@Override
	public void replaceWith(BCPrintableAttribute pa) {
		method.setMspec((MethodSpecification) pa);
	}

	/**
	 * Removes this annotation.
	 */
	@Override
	public void remove() {
		method.setMspec(null);
	}

	/**
	 * Replaces this annotation with the one parsed from
	 * given String.
	 * 
	 * @param code - correct code of method specification
	 * 		to replace with.
	 * @throws RecognitionException - if <code>code</code>
	 * 		is not correct method specification.
	 */
	@Override
	public void parse(String code) throws RecognitionException {
		parse(method.getBcc(), method, null, -1, code);
	}

	/**
	 * @return Simple string represenatations of attribute,
	 * 		for use in debugger only.
	 */
	@Override
	public String toString() {
		return "method specification of " + method.toString();
	}

	/**
	 * Saves method specification to BCEL's Unknown attribute.
	 * 
	 * @param aw - stream to save to.
	 */
	public void save(AttributeWriter aw) {
		precondition.write(aw);
		aw.writeAttributeCount(specCases.length);
		for (int i = 0; i < specCases.length; i++)
			specCases[i].write(aw);
	}

	/**
	 * @return nameIndex of BCEL's Unknown
	 * 		attribute it represents.
	 */
	public int getIndex() {
		return method.getBcc().getCp().findConstant(IDisplayStyle.__mspec);
	}

	/**
	 * @return Unknown (BCEL) attribute name.
	 */
	public String getName() {
		return IDisplayStyle.__mspec;
	}

}
