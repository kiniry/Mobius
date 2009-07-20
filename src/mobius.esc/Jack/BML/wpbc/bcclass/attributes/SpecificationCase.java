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
import formula.atomic.Predicate0Ar;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class SpecificationCase {
	private Formula precondition;
	private Formula postcondition;
	private ExsuresTable exsures;
	private ModifiesSet modifies;
	
	private Formula invariant;
	private Formula historyConstraint;
	private Formula modifiedPostcondition;

	public SpecificationCase(
		Formula precondition,
		Formula postcondition,
		ModifiesSet modifies,
		ExsuresTable exsures) {
		this.precondition = precondition;
		this.postcondition = postcondition;
		this.modifies = modifies;
		this.exsures = exsures;
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
		
		
		if ( (invariant != null)&&(invariant != Predicate0Ar.TRUE) ) {
			postcondition = Formula.getFormula( invariant, postcondition, Connector.AND);
		} 
		return postcondition;
	}

	/**
	 * @return
	 */
	public Formula getPrecondition() {
		return precondition;
	}
	
/*	public void setInvariant(Formula _invariant) {
		invariant = _invariant;
	}
	*/

	/**
	 * @param invariant2
	 */
	public void setHistoryConstraint(Formula _historyConstraint) {
		 historyConstraint = _historyConstraint;
	}

	
	
}
