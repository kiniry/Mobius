/**
 * 
 */
package mobius.directVCGen.vcgen.intern;

import java.util.Vector;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.Variable;

public class ExprResult {
	/** the result of the expression */
	public IFormula res;
	/** the current postcondition */
	public IFormula post;
	
	/** the side conditions generated */
	public IFormula sc;
	
	/** variables to bind due to the side conditions */
	public final Vector<Variable> vars = new Vector<Variable>();
	
	public String toString() {
		return "result:" + res + "\npostcondition : " + post;
	}
}