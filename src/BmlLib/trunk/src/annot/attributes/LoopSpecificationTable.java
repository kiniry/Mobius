package annot.attributes;

import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.modifies.ModifyList;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.IDisplayStyle;
import annot.bcexpression.formula.AbstractFormula;

/**
 * This class represents "loop specification table" method
 * attribute. It is used only in saving to / loading from
 * JavaClass.
 * 
 * @author tomekb
 */
public class LoopSpecificationTable extends BCAttributeTable {

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
	public LoopSpecificationTable(BCMethod m, BCAttributeMap parent) {
		super(m, parent);
	}

	@Override
	public String getName() {
		return IDisplayStyle.__loopSpecTable;
	}

	@Override
	protected InCodeAttribute loadSingle(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		ModifyList modifies = new ModifyList(ar);
		AbstractFormula invariant = ar.readFormula();
		BCExpression decreases = ar.readExpression();
		return new SingleLoopSpecification(m, null, -1, modifies, invariant, decreases);
	}

	@Override
	protected int singleType() {
		return AType.C_LOOPSPEC;
	}

}
