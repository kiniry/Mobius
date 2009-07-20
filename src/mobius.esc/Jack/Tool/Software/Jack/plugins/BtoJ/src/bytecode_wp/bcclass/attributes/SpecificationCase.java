/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcclass.attributes;

import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
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
	
	public void setMethodSpecification( MethodSpecification _mSpec) {
		mSpec = _mSpec;
	}
	
	public MethodSpecification getMethodSpecification( ) {
		return mSpec;
	}
	
	/**
	 * @return
	 */
	public ExsuresTable getExsures() {
		/*exsures.setModifiedPostCondition(getModifiesPostcondition());*/
		return exsures;
	}

	/**
	 * @return
	 */
	public ModifiesSet getModifies() {
		return modifies;
	}


	/**
	 * @return
	 */
	public Formula getPostcondition() {
		Formula postcondition = (Formula)this.postcondition.getPostconditionOnMethodCall();
		return postcondition;
	}

	/**
	 * @return
	 */
	public Formula getPrecondition() {
		return precondition;
	}
	


	/**
	 * generate and return the predicate that must hold in the post state 
	 * of the method in case of normal termination
	 * @param vcg TODO
	 * @return
	 */
	public void getPostconditionToProve(VCGPath vcg) {
		postcondition.getPostconditionToProve(vcg, VcType.NORM_POST);
		/*Formula postconditionToProve = postcondition.getPostconditionToProve(vcg);*/
		/*return postconditionToProve;*/
	}
}
