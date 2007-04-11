package mobius.directVCGen.formula.expression.bool;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class BEqualRef extends APrefixExpr {
	public final static FunType fullType = new FunType(Type.refs,
											new FunType(Type.refs,
												new FunType(Type.bool)));
	BEqualRef(Vector<IFormula> args) {
		super("beqn", args, fullType);
	}
	
	public IFormula clone(Vector<IFormula> args) {
		return new BEqualRef(args);
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitBEqualRef(this);
	}

	public int getID() {
		return bEqualRef;
	}
}
