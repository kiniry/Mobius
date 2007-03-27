package mobius.directVCGen.formula.expression.numfloat;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class FFloat extends APrefixExpr{

	public final static FunType fullType =
			new FunType(Type.num, new FunType(Type.num,
					new FunType(Type.num)));
	
	public FFloat(Vector<IFormula> args) {
		super("iadd", args, fullType);
	}

	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new FFloat(args);
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitFFloat(this);
		
	}

	public int getID() {
		return fFloat;
	}

}
