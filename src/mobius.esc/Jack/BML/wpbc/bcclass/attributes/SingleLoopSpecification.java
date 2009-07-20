/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass.attributes;

import bcexpression.Expression;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class SingleLoopSpecification {
	// the cp index in the bytecode that corresponds to the beginning of the loop
	private int cpIndex;
	private Formula invariant;
	private ModifiesSet modifies;
	private Expression decreases;
	
	public SingleLoopSpecification(int _cpIndex, ModifiesSet _modifies, Formula _invariant, Expression _decreases) {
		cpIndex  = _cpIndex;
		invariant = _invariant;
		decreases = _decreases;
		modifies = _modifies;
	}

	/**
	 * @return
	 */
	public Expression getDecreases() {
		return decreases;
	}

	/**
	 * @return
	 */
	public Formula getInvariant() {
		return invariant;
	}

	/**
	 * @return
	 */
	public ModifiesSet getModifies() {
		return modifies;
	}



	/**
	 * @param formula
	 */
	public void setInvariant(Formula formula) {
		invariant = formula;
	}

	/**
	 * @return the index in the bytecode at which the loop that is 
	 *  specified with this invariant starts
	 */
	public int getCpIndex() {
		return cpIndex;
	}
}
