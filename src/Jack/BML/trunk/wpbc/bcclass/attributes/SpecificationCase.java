/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass.attributes;

import modifexpression.ModifiesExpression;
import bcexpression.Expression;
import formula.Connector;
import formula.Formula;
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
	private ModifiesExpression[] modifies;
	
	private Formula modifiedPostcondition;

	public SpecificationCase(
		Formula precondition,
		Formula postcondition,
		ModifiesExpression[] modifies,
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
		exsures.setModifiedPostCondition(getModifiesPostcondition());
		return exsures;
	}

	/**
	 * @return
	 */
	public ModifiesExpression[] getModifies() {
		return modifies;
	}

	public Formula getModifiesPostcondition() {
		if (modifiedPostcondition != null) {
			return modifiedPostcondition;
		}
		ModifiesExpression[] mExpr = getModifies();
		if (mExpr == null ) {
			return postcondition;
		} 
		Formula modPost = Predicate0Ar.TRUE;
		for (int i = 0; i < mExpr.length; i++) {
			Formula f = (Formula)mExpr[i].getPostCondition();
			if ( f == null) {
				continue;
			}
			modPost = Formula.getFormula(modPost, f, Connector.AND);
		}
		modifiedPostcondition = modPost;
		return modifiedPostcondition;
	}
	
	/**
	 * @return
	 */
	public Formula getPostcondition() {
		Formula modPost = getModifiesPostcondition();
		if ( modPost != Predicate0Ar.TRUE) {
			postcondition = Formula.getFormula(postcondition , modPost , Connector.AND);
		}
		return postcondition;
	}

	/**
	 * @return
	 */
	public Formula getPrecondition() {
		return precondition;
	}
}
