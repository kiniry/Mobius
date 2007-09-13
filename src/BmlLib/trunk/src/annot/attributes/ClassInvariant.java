package annot.attributes;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.formula.AbstractFormula;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

public class ClassInvariant extends BCPrintableAttribute implements
		IBCAttribute {

	private BCClass bcc;
	private AbstractFormula invariant;

	public ClassInvariant(BCClass bcc) {
		this.bcc = bcc;
		this.invariant = Predicate0Ar.TRUE;
	}

	public ClassInvariant(BCClass bcc, AbstractFormula invariant) {
		this.bcc = bcc;
		this.invariant = invariant;
	}

	public ClassInvariant(BCClass bcc, AttributeReader ar)
			throws ReadAttributeException {
		this.bcc = bcc;
		this.invariant = (AbstractFormula) ar.readExpression();
	}

	@Override
	public String printCode1(BMLConfig conf) {
		String code = invariant.printLine(conf, IDisplayStyle._classInvariant);
		return "\n" + conf.addComment(code);
	}

	@Override
	public void replaceWith(BCPrintableAttribute pa) {
		bcc.invariant = (ClassInvariant) pa;
	}

	@Override
	public void remove() {
		bcc.invariant = null;
	}

	@Override
	public void parse(String code) throws RecognitionException {
		parse(bcc, null, null, -1, code);
	}

	@Override
	public String toString() {
		return "class invariant";
	}

	public int getIndex() {
		return bcc.cp.findConstant(IDisplayStyle.__classInvariant);
	}

	public String getName() {
		return IDisplayStyle.__classInvariant;
	}

	public void save(AttributeWriter aw) {
		invariant.write(aw);
	}

}
