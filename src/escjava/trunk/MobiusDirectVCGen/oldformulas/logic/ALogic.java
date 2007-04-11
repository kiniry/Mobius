package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.AFormula;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.type.Type;



/**
 * The class representing a logic formula, a formula of type prop.
 * All logic formula should extend this class.
 * @author J. Charles
 */
public abstract class ALogic extends AFormula {

	/**
	 * The default constructor. It basically sets the type to prop.
	 */
	public ALogic() {
		this(new Vector<IFormula>());
	}
	
	/**
	 * A constructor setting the args (children) of the formula.
	 * @param args The arguments of the formula to build.
	 */
	public ALogic(Vector<IFormula> args) {
		super(Type.prop, args);
	}

	/**
	 * Helper method to format *nicely* the given string surrounding
	 * it with its type.
	 * @param mid the key to format
	 * @return the nice formatted string
	 */
	protected String formatWithType(String mid) {
		return "" + mid + ":" + getType();
	}
}
