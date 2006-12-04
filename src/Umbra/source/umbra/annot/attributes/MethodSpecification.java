/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package umbra.annot.attributes;

import umbra.annot.formula.Predicate0Ar;
import umbra.annot.formula.Formula;

/*import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Predicate0Ar;*/

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class MethodSpecification /*implements BCAttribute*/ {
	
	private Formula precondition;
	
	/*private ClassInvariant invariant;
	private Formula historyConstraint;
	
	private Formula returnBoolConstraints;*/
	private SpecificationCase[] specificationCases;
	
	public MethodSpecification(Formula precondition, SpecificationCase[] specificationCases) {
		this.precondition = precondition;
		this.specificationCases = specificationCases;
		//init();
		
	}
	
	private void init() {		
		if (specificationCases == null) {
			return;
		}
		for (int i = 0; i < specificationCases.length; i++) {
			specificationCases[i].setMethodSpecification(this);
		}
	}

	public SpecificationCase[] getSpecificationCases() {
		return specificationCases;
	}

	
	/**
	 * @return
	 */
	public Formula getPrecondition() {
		return (Formula)precondition.copy();
	}


	/**
	 * get the contract precondition for calling methods
	 * @return
	 */
	/*public Formula getDesugaredPrecondition() {
		if ( specificationCases == null) {
			return (Formula)precondition.copy();
		}
		Formula desugaredPre = Predicate0Ar.TRUE;
		for (int i = 0; i < specificationCases.length; i++) {
			Formula casePrecondition = (Formula)specificationCases[i].getPrecondition().copy();
			Formula casePre = (Formula)casePrecondition.copy();
			desugaredPre = Formula.getFormula( desugaredPre , casePre , Connector.OR);
		}
		
		desugaredPre = Formula.getFormula(( Formula)(precondition.copy()), desugaredPre, Connector.AND);
		return desugaredPre;
	}
	
	public Formula getInvariant() {
		if (invariant == null) {
			return Predicate0Ar.TRUE;
		}
		return invariant.getClassInvariant();
	}
	

	public Formula getInvariantAfterInit() {
		if (invariant == null) {
			return Predicate0Ar.TRUE;
		}
		return invariant.getClassInvariantAfterInit();
	}
    
	public void setInvariant(ClassInvariant invariant) {
		this.invariant = invariant;
	}
	public Formula getHistoryConstraint() {
		return historyConstraint;
	}
	public void setHistoryConstraint(Formula historyConstraint) {
		this.historyConstraint = historyConstraint;
	}

	
	public void setReturnBoolConstraints(Formula resultBoolConstraints) {
		returnBoolConstraints = resultBoolConstraints;
	}


public Formula getReturnBoolConstraints() {
	return returnBoolConstraints;
}*/
	
	public String printCode() {
		String code = "/*\n";
		if (precondition != null)
			if (precondition != Predicate0Ar.TRUE)
				code += " *  requires " + precondition.toString() + "\n";
		for (int i=0; i < specificationCases.length; i++)
			code += specificationCases[i].printCode();
		return code + " */\n";
	}

}
