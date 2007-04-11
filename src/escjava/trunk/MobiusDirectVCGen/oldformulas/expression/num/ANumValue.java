package mobius.directVCGen.formula.expression.num;

import java.util.Vector;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;


public abstract class ANumValue extends APrefixExpr {

	public ANumValue(String name, Vector<IFormula> args, FunType fType) {
		super(name, args, fType);
	}
	public abstract long getNormalValue();

}
