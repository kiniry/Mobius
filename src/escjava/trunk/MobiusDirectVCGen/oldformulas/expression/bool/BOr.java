package mobius.directVCGen.formula.expression.bool;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class BOr extends APrefixExpr {
	public final static FunType fullType = new FunType(Type.bool,
											new FunType(Type.bool,
												new FunType(Type.bool)));
	BOr(Vector<IFormula> args) {
		super("bor", args, fullType);
	}
	
	public IFormula clone(Vector<IFormula> args) {
		return new BOr(args);
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitBOr(this);
	}

	public int getID() {
		return bOr;
	}
}
