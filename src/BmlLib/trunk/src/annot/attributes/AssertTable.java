package annot.attributes;

import annot.bcclass.BCMethod;
import annot.formula.AbstractFormula;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.IDisplayStyle;

/**
 * This class represents "assert table" method attribute.
 * 
 * @author tomekb
 */
public class AssertTable extends BCAttributeTable {

	/**
	 * A constructor.
	 * 
	 * @param m - method containing this attribute,
	 * @param parent - BCAttributeMap containing
	 * 		its attributes.
	 * @see BCAttributeTable#BCAttributeTable(BCMethod, BCAttributeMap)
	 */
	public AssertTable(BCMethod m, BCAttributeMap parent) {
		super(m, parent);
	}

	/**
	 * Loads single assert from file.
	 * 
	 * @param m - method containing this attribute,
	 * @param ar - stream to load from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent correct
	 * 		assert.
	 */
	@Override
	protected SingleAssert loadSingle(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		AbstractFormula f = (AbstractFormula) ar.readExpression();
		SingleAssert sa = new SingleAssert(m, null, -1, f);
		return sa;
	}

	/**
	 * @return Unknown (BCEL) attribute name.
	 */
	@Override
	public String getName() {
		return IDisplayStyle.__assertTable;
	}

	/**
	 * @return attribute type of single annotation. 
	 */
	@Override
	protected int singleType() {
		return AType.C_ASSERT;
	}

}
