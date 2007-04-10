/**
 * 
 */
package mobius.directVCGen.vcgen.intern;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.Variable;

public class ExprResult {
	/** the temporary variable; used in the vcGen of expressions */
	public Variable vtmp;
	/** the current postcondition */
	public IFormula post;
	
	/** the excp post condition... */
	public IFormula excpost;
	
	public void substWith(IFormula f) {
		post.subst(vtmp, f);
	}
	
	public String toString() {
		if(vtmp != null) {
			return "temp var:" + vtmp  + "\npostcondition : " + post;
		}
		return  "\npostcondition : " + post;
	}
}