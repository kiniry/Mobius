package annot.formula;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;
import annot.bcio.AttributeReader;

// atrapa Formula
public class UnknownFormula extends Formula {

	String opis;

	public UnknownFormula() {
		opis = "?";
	}
	
	public UnknownFormula(String opis) {
		AttributeReader.ok = false;
		this.opis = opis;
	}
	
	public Expression copy() {
		return this;
	}

	public Expression substitute(Expression _e1, Expression _e2) {
		return this;
	}

	public String toString() {
		System.out.println("unimplemented: " + opis);
		return "?";
	}
	
	public String printCode1(BMLConfig conf) {
		return toString();
	}

}
