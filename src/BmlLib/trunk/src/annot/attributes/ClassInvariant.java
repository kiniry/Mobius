package annot.attributes;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.formula.AbstractFormula;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Parsing;

/**
 * This class represents class invariant attribute.
 * 
 * @author tomekb
 */
public class ClassInvariant extends ClassAttribute implements
		IBCAttribute {

	/**
	 * BCClass contaning this attribute.
	 */
	private BCClass bcc;

	/**
	 * The invariant formula.
	 */
	private ExpressionRoot<AbstractFormula> invariant;

	/**
	 * Creates empty class invariant (with formula 'true').
	 * 
	 * @param bcc - BCClass containign this invariant.
	 */
	public ClassInvariant(BCClass bcc) {
		this.bcc = bcc;
		this.invariant = new ExpressionRoot<AbstractFormula>(this, new Predicate0Ar(true));
	}

	/**
	 * A Constructor from BCClass and AbstractFormula.
	 * 
	 * @param bcc - BCClass containing this invariant,
	 * @param invariant - a invariant formula.
	 */
	public ClassInvariant(BCClass bcc, AbstractFormula invariant) {
		this.bcc = bcc;
		this.invariant = new ExpressionRoot<AbstractFormula>(this, invariant);
	}

	/**
	 * A constructor from attributeReader, for use in class
	 * loading only.
	 * 
	 * @param bcc - BCClass containing this invariant,
	 * @param ar - stream to load invariant from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		class invariant.
	 */
	public ClassInvariant(BCClass bcc, AttributeReader ar)
			throws ReadAttributeException {
		this.bcc = bcc;
		this.invariant = new ExpressionRoot<AbstractFormula>(this, ar.readFormula());
	}

	/**
	 * Prints annotation's code to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of this invariant.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		String code = invariant.printLine(conf, IDisplayStyle._classInvariant);
		return "\n" + Parsing.addComment(code);
	}

	/**
	 * Replaces this annotation with a given one, updating
	 * nessesery references in BCClass.
	 * 
	 * @param pa - annotation to replace with.
	 */
	@Override
	public void replaceWith(BCPrintableAttribute pa) {
		bcc.setInvariant((ClassInvariant) pa);
	}

	/**
	 * Replaces existing class invariant in given
	 * BCClass with this attribute.
	 * 
	 * @param bcc - BCClass to place this attribute as it's
	 * 		class invariant.
	 */
	@Override
	public void replace(BCClass bcc) {
		bcc.setInvariant(this);
	}

	/**
	 * Removes this annotation.
	 */
	@Override
	public void remove() {
		bcc.setInvariant(null);
	}

	/**
	 * Replaces this annotation with the one parsed from
	 * given String.
	 * 
	 * @param code - correct code of class invariant
	 * 		to replace with.
	 * @throws RecognitionException - if <code>code</code>
	 * 		is not correct class invariant's code.
	 */
	@Override
	public void parse(String code) throws RecognitionException {
		parse(bcc, null, null, -1, code);
	}

	/**
	 * @return Simple string represenatations of attribute,
	 * 		for use in debugger only.
	 */
	@Override
	public String toString() {
		return "class invariant";
	}

	/**
	 * @return nameIndex of BCEL's Unknown
	 * 		attribute it represents.
	 */
	public int getIndex() {
		return bcc.getCp().findConstant(IDisplayStyle.__classInvariant);
	}

	/**
	 * @return Unknown (BCEL) attribute name.
	 */
	public String getName() {
		return IDisplayStyle.__classInvariant;
	}

	/**
	 * Saves this annotation to BCEL's Unknown attribute,
	 * using attributeWriter.
	 * @param aw - stream to save to.
	 */
	public void save(AttributeWriter aw) {
		invariant.write(aw);
	}

	/**
	 * @return the invariant formula.
	 */
	public AbstractFormula getInvariant() {
		return invariant.getExpression();
	}

	@Override
	public ExpressionRoot[] getAllExpressions() {
		ExpressionRoot[] all = new ExpressionRoot[1];
		all[0] = invariant;
		return all;
	}

}
