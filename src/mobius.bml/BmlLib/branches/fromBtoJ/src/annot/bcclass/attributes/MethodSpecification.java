package annot.bcclass.attributes;

import annot.bcclass.BMLConfig;
import annot.formula.Formula;
import annot.formula.Predicate0Ar;

//import annot.formula.Connector;
//import annot.formula.Formula;
//import annot.formula.Predicate0Ar;

public class MethodSpecification extends BCPrintableAttribute implements BCAttribute{
	private Formula precondition;
//	private ClassInvariant invariant;
//	private Formula historyConstraint;
//	private Formula returnBoolConstraints;
	private SpecificationCase[] specificationCases;
	
	public MethodSpecification(Formula precondition, SpecificationCase[] specificationCases) {
		this.atype = "method spec ";
		this.precondition = precondition;
		this.specificationCases = specificationCases;
		init();
	}
	
	public String printCode(BMLConfig conf) {
		conf.indent = "";
		String code = "";
		if (precondition != null)
			if (precondition != Predicate0Ar.TRUE)
				code += conf.newLine() + "requires " + precondition.printLine(conf, 11);
		for (int i=0; i < specificationCases.length; i++)
			code += specificationCases[i].printCode(conf);
		if (code.indexOf("\n") < 0)
			return "";
		return conf.addComment(code);
	}

	private void init() {		
		if (specificationCases == null) {
			return;
		}
		for (int i = 0; i < specificationCases.length; i++) {
			specificationCases[i].setMethodSpecification(this);
		}
	}

	@Override
	public void replaceWith(BCPrintableAttribute attr) {
		method.setMethodSpecification((MethodSpecification)attr);
	}

//
//
//	/**
//	 * @return
//	 */
//	public SpecificationCase[] getSpecificationCases() {
//		return specificationCases;
//	}
//
//	
//	/**
//	 * @return
//	 */
//	public Formula getPrecondition() {
//		return (Formula)precondition.copy();
//	}
//
//
//	/**
//	 * get the contract precondition for calling methods
//	 * @return
//	 */
//	public Formula getDesugaredPrecondition() {
//		if ( specificationCases == null) {
//			return (Formula)precondition.copy();
//		}
//		Formula desugaredPre = Predicate0Ar.TRUE;
//		for (int i = 0; i < specificationCases.length; i++) {
//			Formula casePrecondition = (Formula)specificationCases[i].getPrecondition().copy();
//			Formula casePre = (Formula)casePrecondition.copy();
//			desugaredPre = Formula.getFormula( desugaredPre , casePre , Connector.OR);
//		}
//		
//		desugaredPre = Formula.getFormula(( Formula)(precondition.copy()), desugaredPre, Connector.AND);
//		return desugaredPre;
//	}
//	
//	/**
//	 * @return Returns the invariant.
//	 */
//	public Formula getInvariant() {
//		if (invariant == null) {
//			return Predicate0Ar.TRUE;
//		}
//		return invariant.getClassInvariant();
//	}
//	
//
//	/**
//	 * @return Returns the invariant.
//	 */
//	public Formula getInvariantAfterInit() {
//		if (invariant == null) {
//			return Predicate0Ar.TRUE;
//		}
//		return invariant.getClassInvariantAfterInit();
//	}
//    
//	/**
//	 * @param invariant The invariant to set.
//	 */
//	public void setInvariant(ClassInvariant invariant) {
//		this.invariant = invariant;
//	}
//	/**
//	 * @return Returns the historyConstraint.
//	 */
//	public Formula getHistoryConstraint() {
//		return historyConstraint;
//	}
//	/**
//	 * @param historyConstraint The historyConstraint to set.
//	 */
//	public void setHistoryConstraint(Formula historyConstraint) {
//		this.historyConstraint = historyConstraint;
//	}
//
//	
///**
// * add constraints about the return type
// * @param resultBoolConstraints
// */
//	public void setReturnBoolConstraints(Formula resultBoolConstraints) {
//		returnBoolConstraints = resultBoolConstraints;
//	}
//
//
///**
// * @return Returns the returnBoolConstraints.
// */
//public Formula getReturnBoolConstraints() {
//	return returnBoolConstraints;
//}
}
