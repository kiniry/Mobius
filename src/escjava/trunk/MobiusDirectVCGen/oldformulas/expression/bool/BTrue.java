package mobius.directVCGen.formula.expression.bool;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class BTrue extends APrefixExpr {
	public final static FunType fullType = new FunType(Type.bool);
					
	BTrue() {
		super("true", new Vector<IFormula>(), fullType);
	}
	
	public IFormula clone(Vector<IFormula> args) {
		return new BTrue();
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitBTrue(this);
	}

	public int getID() {
		return bTrue;
	}
}
