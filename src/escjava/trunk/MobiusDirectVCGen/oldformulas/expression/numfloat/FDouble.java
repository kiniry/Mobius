package mobius.directVCGen.formula.expression.numfloat;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class FDouble extends APrefixExpr{

	public final static FunType fullType =
			new FunType(Type.num, new FunType(Type.num,
					new FunType(Type.num)));
	
	public FDouble(Vector<IFormula> args) {
		super("iadd", args, fullType);
	}

	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new FDouble(args);
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitFDouble(this);
		
	}

	public int getID() {
		// TODO Auto-generated method stub
		return 0;
	}

}
