package mobius.directVCGen.formula.expression.ref;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.APrefixExpr;
import mobius.directVCGen.formula.type.FunType;
import mobius.directVCGen.formula.type.Type;


public class RNull extends APrefixExpr{

	public final static FunType fullType =
					new FunType(Type.refs);
	
	public RNull() {
		super("null", new Vector<IFormula>(), fullType);
	}

	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new RNull();
	}

	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitRNull(this);
		
	}

	public int getID() {
		return rNull;
	}

}
