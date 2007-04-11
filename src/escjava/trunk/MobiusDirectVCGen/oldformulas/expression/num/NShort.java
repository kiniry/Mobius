package mobius.directVCGen.formula.expression.num;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class NShort extends ANumValue {

	public final static FunType fullType =
			new FunType(Type.numShort);
	private final short fValue;
	
	public NShort(short value) {
		super("" + value, new Vector<IFormula>(), fullType);
		fValue = value;
	}

	public short getValue() {
		return fValue;
	}
	
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new NShort(getValue());
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitNShort(this);
		
	}

	public int getID() {
		return nShort;
	}

	@Override
	public long getNormalValue() {
		return fValue;
	}

}
