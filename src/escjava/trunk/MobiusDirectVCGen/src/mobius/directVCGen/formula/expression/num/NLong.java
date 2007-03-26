package mobius.directVCGen.formula.expression.num;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class NLong extends ANumValue {

	public final static FunType fullType =
			new FunType(Type.numLong);
	private final long fValue;
	
	public NLong(long value) {
		super("" + value, new Vector<IFormula>(), fullType);
		fValue = value;
	}

	public long getValue() {
		return fValue;
	}
	
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new NLong(getValue());
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitNLong(this);
		
	}

	public int getID() {
		return nLong;
	}

	@Override
	public long getNormalValue() {
		return fValue;
	}

}
