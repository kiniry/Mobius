/*
 * Created on Sep 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;

import bcclass.BCConstantPool;
import bcexpression.Expression;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ModifiesIdent extends ModifiesExpression {
	
	public ModifiesIdent(Expression  ident, BCConstantPool _constantPool) {
		super(ident , _constantPool);
	}

	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getCondition()
	 */
	public Expression getPostCondition(int state) {
		/*Variable o = new Variable(FreshIntGenerator.getInt() );
		Predicate2Ar condition = new Predicate2Ar( o, expr, PredicateSymbol.NOTEQ);
		Formula p = new Predicate2Ar(o, new OLD(o), PredicateSymbol.EQ);
		Formula f = Formula.getFormula(condition, p, Connector.IMPLIES );
		Quantificator q = new Quantificator(Quantificator.FORALL, o );
		QuantifiedFormula for_all_o = new QuantifiedFormula(f, q );
		return for_all_o;*/
		return Predicate0Ar.TRUE;
	}
	
	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getModifiedExpression()
	 */
	public Expression getExpression() {
		
		return getSubExpressions()[0];
	}



	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		// TODO Auto-generated method stub
		return null;
	}
	
	public ModifiesExpression getModifies() {
		return null;
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		// TODO Auto-generated method stub
		return "modifiesIdent " + getSubExpressions()[0];
	}


	

}
