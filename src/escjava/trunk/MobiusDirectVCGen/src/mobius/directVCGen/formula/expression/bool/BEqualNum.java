package mobius.directVCGen.formula.expression.bool;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class BEqualNum extends APrefixExpr {
	public final static FunType fullType = new FunType(Type.num,
											new FunType(Type.num,
												new FunType(Type.bool)));
	BEqualNum(Vector<IFormula> args) {
		super("beqn", args, fullType);
	}
	
	public IFormula clone(Vector<IFormula> args) {
		return new BEqualNum(args);
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitBEqualNum(this);
	}

	public int getID() {
		return bEqualNum;
	}
}
