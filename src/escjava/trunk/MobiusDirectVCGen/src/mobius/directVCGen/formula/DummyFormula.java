/**
 * 
 */
package mobius.directVCGen.formula;

import java.util.Vector;

import mobius.directVCGen.formula.type.Type;


public class DummyFormula extends AFormula {

	public DummyFormula(Vector<IFormula> args) {
		super(Type.undef, args);
	}

	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new DummyFormula(args);
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitDummyFormula(this);
	}

	public int getID() {
		return dummy;
	}
	
	public String toString() {
		String res = "dummy (";
		for (IFormula f: this) {
			res += " " + f;
		}
		return res + ")";
	}
}