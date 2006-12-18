package umbra.annot.modifexpression;

import umbra.annot.bcclass.BCClass;
import umbra.annot.bcexpression.BCLocalVariable;
import umbra.annot.bcexpression.Expression;
import umbra.annot.formula.Predicate0Ar;

public class ModifiesLocalVariable extends  ModifiesIdent {

	/**
	 * @param ident
	 * @param _constantPool
	 */
	public ModifiesLocalVariable(BCLocalVariable localVar, BCClass _clazz) {
		super(localVar, _clazz);
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
	    return Predicate0Ar.TRUE;
//		BCLocalVariable locvar = (BCLocalVariable)getSubExpressions()[0];
//		Formula f = new Predicate2Ar( locvar, locvar.atState( state) , PredicateSymbol.EQ); 
//		return f;
	}
}
