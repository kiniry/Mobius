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
public class SingleBlockSpecification {

	private int startCpIndex;
	private int endCpIndex;
	private Formula precondition;
	private Formula postcondition;
	private Expression[] modifies;
	
	public SingleBlockSpecification(int _startCpInd, int _endCpInd, Formula _precondition, Expression[] _modifies, Formula _postcondition) {
		startCpIndex = _startCpInd;
		endCpIndex = _endCpInd;
		precondition = _precondition;
		postcondition = _postcondition;
		modifies = _modifies;
	}
	/**
	 * @return
	 */
	public int getEndCpIndex() {
		return endCpIndex;
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

	/**
	 * @return
	 */
	public int getStartCpIndex() {
		return startCpIndex;
	}

	/**
	 * @param i
	 */
	public void setEndCpIndex(int i) {
		endCpIndex = i;
	}

	/**
	 * @param expressions
	 */
	public void setModifies(Expression[] expressions) {
		modifies = expressions;
	}

	/**
	 * @param formula
	 */
	public void setPostcondition(Formula formula) {
		postcondition = formula;
	}

	/**
	 * @param formula
	 */
	public void setPrecondition(Formula formula) {
		precondition = formula;
	}

	/**
	 * @param i
	 */
	public void setStartCpIndex(int i) {
		startCpIndex = i;
	}

}
