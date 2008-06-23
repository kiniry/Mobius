package annot.attributes;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Parsing;
import annot.bcexpression.formula.AbstractFormula;

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
   * The flag which is <code>true</code> in case the invariant is
   * an instance invariant and <code>false</code> otherwise.
   */
	private boolean isInstance;

  /**
   * The flag which contains the access flags for the current class
   * invariant.
   */
  private int access_flags;

	/**
	 * Creates empty invariant (with formula 'true').
	 * 
	 * @param bcc - BCClass containing this invariant.
	 * @param instanceflag - <code>true</code> in case the invariant is an
	 *   instance invariant
	 */
	public ClassInvariant(BCClass bcc, boolean instanceflag) {
		this.bcc = bcc;
		this.invariant = new ExpressionRoot<AbstractFormula>(this, new Predicate0Ar(true));
		this.isInstance = instanceflag;
		commitInstanceFlag();
	}

	/**
	 * A Constructor from BCClass and AbstractFormula.
	 * 
	 * @param bcc - BCClass containing this invariant,
	 * @param invariant - a invariant formula.
	 * @param instanceflag - <code>true</code> in case the invariant is an
   *   instance invariant
	 */
	public ClassInvariant(BCClass bcc, AbstractFormula invariant,
	                      boolean instanceflag) {
		this.bcc = bcc;
		this.invariant = new ExpressionRoot<AbstractFormula>(this, invariant);
		this.isInstance = instanceflag;
		commitInstanceFlag();
	}

	/**
	 * This method propagates the {@link #isInstance} flag to the
	 * access_flags field.
	 */
	private void commitInstanceFlag() {
	  if (!isInstance) {
	    access_flags = access_flags | AttributeFlags.ACC_STATIC;
	  }
  }

  /**
	 * A constructor from attributeReader, for use in class
	 * loading only.
	 * 
	 * @param bcc - BCClass containing this invariant,
	 * @param ar - {@link AttributeReader} to load invariant from, it is
	 *   in a position right after the length field of the attribute
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		class invariant.
	 */
	public ClassInvariant(BCClass bcc, AttributeReader ar)
			throws ReadAttributeException {
		this.bcc = bcc;
		access_flags = ar.readShort();
		isInstance = (access_flags & AttributeFlags.ACC_STATIC) == 0;
		this.invariant = new ExpressionRoot<AbstractFormula>(this,
		  ar.readFormula());
	}

	/**
	 * Prints the code of the annotation to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of this invariant.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
	  String header = isInstance ? IDisplayStyle._classInvariant :
	    IDisplayStyle._staticInvariant;
		String code = invariant.printLine(conf, header);
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
		bcc.remove(getAccessFlags());
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
	  if (isInstance) {
	    return "invariant";
	  } else {
	    return "class invariant";
	  }
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
   * @return the access flags for the current invariant
   */
  public int getAccessFlags() {
    return access_flags;
  }

	/**
	 * Saves this annotation to BCEL's Unknown attribute,
	 * using attributeWriter.
	 * @param aw - stream to save to.
	 */
	public void save(AttributeWriter aw) {
	  aw.writeShort(access_flags);
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

	/**
	 * Return the information if the invariant is instance/static
	 *
	 * @return <code>true</code> in case the invariant is an instance
	 *   invariant, <code>false</code> otherwise
	 */
  public boolean isInstance() {
    return isInstance;
  }
}
