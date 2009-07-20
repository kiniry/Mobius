/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass.attributes;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class MethodSpecification implements BCAttribute {
	
	private Formula precondition;
	private SpecificationCase[] specificationCases;
	
	public MethodSpecification(Formula precondition, SpecificationCase[] specificationCases) {
		this.precondition = precondition;
		this.specificationCases = specificationCases;
	}
	


	public void setHistoryConstraint(Formula invariant) {
		if (specificationCases == null) {
			return;
		}		
		for (int i = 0; i < specificationCases.length; i++ ) {
			specificationCases[i].setHistoryConstraint(invariant);
		}
	}


	/**
	 * @return
	 */
	public SpecificationCase[] getSpecificationCases() {
		return specificationCases;
	}

	
	/**
	 * @return
	 */
	public Formula getPrecondition() {
		return precondition;
	}


}
