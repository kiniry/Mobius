/*
 * Created on Sep 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;

import bcclass.BCConstantPool;
import bcexpression.BCLocalVariable;
import bcexpression.Expression;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ModifiesLocalVariable extends  ModifiesIdent {

	/**
	 * @param ident
	 * @param _constantPool
	 */
	public ModifiesLocalVariable(BCLocalVariable localVar, BCConstantPool _constantPool) {
		super(localVar, _constantPool);
	}
	
/*	 (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getPostConditionWhenCalled(bcexpression.ConstantVariable)
	 
	public Expression getPostConditionWhenCalled(ValueOfConstantAtState constantVar) {
		Predicate2Ar ref_diff_from_localVar = new Predicate2Ar(constantVar , getSubExpressions()[0], PredicateSymbol.NOTEQ);
		Predicate2Ar ref_eq_old_ref = new Predicate2Ar(constantVar, new OLD( constantVar), PredicateSymbol.EQ);
		
		Formula f = Formula.getFormula( ref_diff_from_localVar, ref_eq_old_ref, Connector.IMPLIES);
		f = Formula.getFormula(f, new Quantificator(Quantificator.FORALL, constantVar ) );
		
		return f;
	}
*/
	public BCLocalVariable getLocalVariable() {
		return (BCLocalVariable)getSubExpressions()[0];
	}
	
	public  Expression getPostCondition(int state) {
		BCLocalVariable locvar = (BCLocalVariable)getSubExpressions()[0];
		Formula f = new Predicate2Ar( locvar, locvar.atState( state) , PredicateSymbol.EQ); 
		return f;
	}
}
