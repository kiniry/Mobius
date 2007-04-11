/**
 * 
 */
package mobius.directVCGen.vcgen.intern;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class ExprResult {
	/** the temporary variable; used in the vcGen of expressions */
	public QuantVariableRef vtmp;
	/** the current postcondition */
	public Term post;
	
	/** the excp post condition... */
	public Term excpost;
	
	public void substWith(Term f) {
		post.subst(vtmp, f);
	}
	
	public String toString() {
		if(vtmp != null) {
			return "temp var:" + vtmp  + "\npostcondition : " + post;
		}
		return  "\npostcondition : " + post;
	}
}