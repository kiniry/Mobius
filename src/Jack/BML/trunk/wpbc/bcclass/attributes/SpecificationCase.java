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
public class SpecificationCase {
	private Formula precondition;
	private Formula postcondition;
	private ExsuresTable exsures;
	private Expression[] modifies;

	public SpecificationCase(
		Formula precondition,
		Formula postcondition,
		Expression[] modifies,
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
		return exsures;
	}

	/**
	 * @return
	 */
	public Expression[] getModifies() {
		return modifies;
	}

	/**
	 * @return
	 */
	public Formula getPostcondition() {
		return postcondition;
	}

	/**
	 * @return
	 */
	public Formula getPrecondition() {
		return precondition;
	}

}
