package annot.attributes;

import annot.bcclass.BCMethod;
import annot.formula.AbstractFormula;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.IDisplayStyle;

/**
 * This class represents "assert table" method attribute.
 * It is used only in saving to / loading from JavaClass.
 * 
 * @author tomekb
 */
public class AssertTable extends BCAttributeTable {

	/**
	 * A constructor.
	 * 
	 * @param m - method containing this attribute,
	 * @param parent - BCAttributeMap containing
	 * 		its attributes. This attribute can only
	 * 		save to / load atrtbutes from BCEL's Unknown
	 * 		attribute, it doesn't store them itself.
	 * @see BCAttributeTable#BCAttributeTable(BCMethod, BCAttributeMap)
	 */
	public AssertTable(BCMethod m, BCAttributeMap parent) {
		super(m, parent);
	}

	/**
	 * Loads single assert from a file.
	 * 
	 * @param m - a method containing this attribute,
	 * @param ar - a stream to load the assert from.
	 * @throws ReadAttributeException - if data left
	 * 		in <code>ar</code> doesn't represent a correct
	 * 		assert.
	 */
	@Override
	protected SingleAssert loadSingle(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		AbstractFormula f = ar.readFormula();
		SingleAssert sa = new SingleAssert(m, null, -1, f);
		return sa;
	}

	/**
	 * @return Unknown (BCEL) attribute name. TODO unknown dla kogo
	 */
	@Override
	public String getName() {
		return IDisplayStyle.__assertTable;
	}

	/**
	 * @return attribute type of a single annotation. 
	 */
	@Override
	protected int singleType() {
		return AType.C_ASSERT;
	}

}
