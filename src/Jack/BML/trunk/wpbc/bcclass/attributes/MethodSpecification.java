/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass.attributes;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class MethodSpecification implements BCAttribute {
	
	private SpecificationCase[] specificationCases;
	
	public MethodSpecification(SpecificationCase[] specificationCases) {
		this.specificationCases = specificationCases;
	}
	

//	/**
//	 * @return
//	 */
//	public Precondition getPrecondition() {
//		return precondition;
//	}
//
//	/**
//	 * @param precondition
//	 */
//	public void setPrecondition(Precondition precondition) {
//		this.precondition = precondition;
//	}

	/**
	 * @return
	 */
	public SpecificationCase[] getSpecificationCases() {
		return specificationCases;
	}

	
}
