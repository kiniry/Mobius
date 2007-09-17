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

public class MethodSpecification extends BCPrintableAttribute implements
		IBCAttribute {

	private BCMethod method;
	private AbstractFormula precondition;
	private SpecificationCase[] specCases;

	public MethodSpecification(BCMethod m) {
		this(m, Predicate0Ar.TRUE, new SpecificationCase[0]);
	}

	public MethodSpecification(BCMethod m, AbstractFormula precondition,
			SpecificationCase[] sc) {
		this.method = m;
		this.precondition = precondition;
		this.specCases = sc;
	}

	public MethodSpecification(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		this.method = m;
		this.precondition = (AbstractFormula) ar.readExpression();
		int length = ar.readAttributesCount();
		specCases = new SpecificationCase[length];
		for (int i = 0; i < length; i++)
			specCases[i] = new SpecificationCase(m, ar);
	}

	@Override
	public String printCode1(BMLConfig conf) {
		String code = precondition.printLine(conf, IDisplayStyle._requires);
		if (specCases.length > 0)
			for (int i = 0; i < specCases.length; i++)
				code += specCases[i].printCode(conf);
		return Parsing.addComment(code);
	}

	@Override
	public void replaceWith(BCPrintableAttribute pa) {
		method.setMspec((MethodSpecification)pa);
	}

	public void save(AttributeWriter aw) {
		precondition.write(aw);
		aw.writeAttributeCount(specCases.length);
		for (int i = 0; i < specCases.length; i++)
			specCases[i].write(aw);
	}

	public int getIndex() {
		return method.getBcc().getCp().findConstant(IDisplayStyle.__mspec);
	}

	public String getName() {
		return IDisplayStyle.__mspec;
	}

	@Override
	public void remove() {
		method.setMspec(null);
	}

	@Override
	public void parse(String code) throws RecognitionException {
		parse(method.getBcc(), method, null, -1, code);
	}

	@Override
	public String toString() {
		return "method specification of " + method.toString();
	}

}
