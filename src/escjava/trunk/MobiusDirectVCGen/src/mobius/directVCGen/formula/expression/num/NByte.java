package mobius.directVCGen.formula.expression.num;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class NByte extends ANumValue {

	public final static FunType fullType =
			new FunType(Type.numByte);
	private final byte fValue;
	
	public NByte(byte value) {
		super("" + value, new Vector<IFormula>(), fullType);
		fValue = value;
	}

	public byte getValue() {
		return fValue;
	}
	
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new NByte(getValue());
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitNByte(this);
		
	}

	public int getID() {
		return nByte;
	}

	@Override
	public long getNormalValue() {
		return fValue;
	}

}
