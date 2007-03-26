package mobius.directVCGen.formula.expression.num;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class NInt extends ANumValue {

	public final static FunType fullType =
			new FunType(Type.numInt);
	private final int fValue;
	
	public NInt(int value) {
		super("" + value, new Vector<IFormula>(), fullType);
		fValue = value;
	}

	public int getValue() {
		return fValue;
	}
	
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new NInt(getValue());
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitNInt(this);
		
	}

	public int getID() {
		return nInt;
	}

	@Override
	public long getNormalValue() {
		return fValue;
	}

}
