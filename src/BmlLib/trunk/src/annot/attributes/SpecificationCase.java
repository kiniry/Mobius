package annot.attributes;

import annot.bcclass.BCMethod;
import annot.formula.AbstractFormula;
import annot.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

public class SpecificationCase {

	private BCMethod method;
	private AbstractFormula precondition;
	private AbstractFormula postcondition;

	public SpecificationCase(BCMethod m) {
		this.method = m;
		this.precondition = Predicate0Ar.TRUE;
		this.postcondition = Predicate0Ar.TRUE;
	}

	public SpecificationCase(BCMethod m, AbstractFormula precondition,
			AbstractFormula postcondition) {
		this.method = m;
		this.precondition = precondition;
		this.postcondition = postcondition;
	}

	public SpecificationCase(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		this(m);
		this.precondition = (AbstractFormula) ar.readExpression();
		this.postcondition = (AbstractFormula) ar.readExpression();
	}

	public void write(AttributeWriter aw) {
		precondition.write(aw);
		postcondition.write(aw);
	}

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
