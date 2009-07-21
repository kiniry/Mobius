package annot.bcclass.attributes;

import annot.bcclass.BMLConfig;
import annot.formula.Formula;
import annot.formula.Predicate0Ar;

public class SpecificationCase {
	private Formula precondition;
	private Postcondition postcondition;
	private ExsuresTable exsures;
	private ModifiesSet modifies;
	
	private MethodSpecification mSpec;
	
	public SpecificationCase(
		Formula precondition,
		Postcondition postcondition,
		ModifiesSet modifies,
		ExsuresTable exsures) {
		this.precondition = precondition;
		this.postcondition = postcondition;		
		this.modifies = modifies;
		this.exsures = exsures;
		init();
	}

	private void init() {
		if (postcondition != null) {
			postcondition.setSpecificationCase(this);
		}
		if (exsures != null) {
			exsures.setSpecificationCase(this);
		}
	}

	public String printCode(BMLConfig conf) {
		String code = conf.newLine() + "{|";
		conf.incInd();
		if (precondition != Predicate0Ar.TRUE)
			code += conf.newLine() + "requires " + precondition.printLine(conf, 13);
		if (modifies.getModifiesExpressions()[0].printCode(conf) != "\\everything")
			code += conf.newLine() + "modifies " + modifies.printCode(conf, 9);
		if (postcondition.getPostcondition() != Predicate0Ar.TRUE)
			code += conf.newLine() + "ensures " + postcondition.printCode(conf);
		if (exsures != null)
			code += exsures.printCode(conf);
		conf.decInd();
		code += conf.newLine() + "|}";
		if (code.split("\n").length < 4)
			return "";
		return code;
	}
	
	public void setMethodSpecification( MethodSpecification _mSpec) {
		mSpec = _mSpec;
	}
	
//	public MethodSpecification getMethodSpecification( ) {
//		return mSpec;
//	}
//	
//	/**
//	 * @return
//	 */
//	public ExsuresTable getExsures() {
//		/*exsures.setModifiedPostCondition(getModifiesPostcondition());*/
//		return exsures;
//	}
//
//	/**
//	 * @return
//	 */
//	public ModifiesSet getModifies() {
//		return modifies;
//	}
//
//
//	/**
//	 * @return
//	 */
//	public Formula getPostcondition() {
//		Formula postcondition = (Formula)this.postcondition.getPostconditionOnMethodCall();
//		return postcondition;
//	}
//
//	/**
//	 * @return
//	 */
//	public Formula getPrecondition() {
//		return precondition;
//	}
//	
//
//
//	/**
//	 * generate and return the predicate that must hold in the post state 
//	 * of the method in case of normal termination
//	 * @param vcg TODO
//	 * @return
//	 */
//	public void getPostconditionToProve(VCGPath vcg) {
//		postcondition.getPostconditionToProve(vcg, VcType.NORM_POST);
//		/*Formula postconditionToProve = postcondition.getPostconditionToProve(vcg);*/
//		/*return postconditionToProve;*/
//	}
}
