/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcclass.attributes;

import bytecode_wp.bcexpression.Expression;
import bytecode_wp.formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class SingleLoopSpecification {
	// the intrsuction index in the bytecode array that corresponds to the beginning of the loop
	private int pcIndex;
	private Formula invariant;
	private ModifiesSet modifies;
	private Expression decreases;
	
	public SingleLoopSpecification(int _cpIndex, ModifiesSet _modifies, Formula _invariant, Expression _decreases) {
		pcIndex  = _cpIndex;
		invariant = _invariant;
		decreases = _decreases;
		modifies = _modifies;
	}

	/**
	 * @return
	 */
	public Expression getDecreases() {
		return decreases.copy();
	}

	/**
	 * @return
	 */
	public Formula getInvariant() {
		return (Formula)invariant.copy();
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
	public int getLoopIndex() {
		return pcIndex;
	}
}
