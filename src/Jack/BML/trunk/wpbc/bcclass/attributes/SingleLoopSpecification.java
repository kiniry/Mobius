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
	private Expression[] modifies;
	private Formula decreases;
	
	public SingleLoopSpecification(int _cpIndex, Expression[] _modifies, Formula _invariant, Formula _decreases) {
		cpIndex  = _cpIndex;
		invariant = _invariant;
		decreases = _decreases;
		modifies = _modifies;
	}

	/**
	 * @return
	 */
	public Formula getDecreases() {
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
	public Expression[] getModifies() {
		return modifies;
	}

	/**
	 * @param formula
	 */
	public void setDecreases(Formula formula) {
		decreases = formula;
	}

	/**
	 * @param formula
	 */
	public void setInvariant(Formula formula) {
		invariant = formula;
	}

	/**
	 * @param expressions
	 */
	public void setModifies(Expression[] expressions) {
		modifies = expressions;
	}

	/**
	 * @return the index in the bytecode at which the loop that is 
	 *  specified with this invariant starts
	 */
	public int getCpIndex() {
		return cpIndex;
	}

	/**
	 * @param i
	 */
	public void setCpIndex(int i) {
		cpIndex = i;
	}
}
