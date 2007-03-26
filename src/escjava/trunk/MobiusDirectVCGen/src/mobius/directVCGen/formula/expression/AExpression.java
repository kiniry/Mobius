package mobius.directVCGen.formula.expression;

import java.util.Vector;

import mobius.directVCGen.formula.AFormula;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.type.Type;



/**
 * This class must be extended to implement the expressions.
 * @author J. Charles
 */
public abstract class AExpression extends AFormula {

	public AExpression(Type t) {
		super(t);
	}
	
	public AExpression(Type t, Vector<IFormula> args) {
		super(t, args);
	}


}
