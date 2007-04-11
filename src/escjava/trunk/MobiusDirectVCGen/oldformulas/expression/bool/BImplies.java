package mobius.directVCGen.formula.expression.bool;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class BImplies extends APrefixExpr {
	public final static FunType fullType = new FunType(Type.bool,
											new FunType(Type.bool,
												new FunType(Type.bool)));
	BImplies(Vector<IFormula> args) {
		super("bimplies", args, fullType);
	}
	
	public IFormula clone(Vector<IFormula> args) {
		return new BImplies(args);
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitBImplies(this);
	}

	public int getID() {
		return bImplies;
	}
}
