/*
 * Created on Sep 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;


import utils.FreshIntGenerator;
import utils.Util;
import bcclass.BCConstantPool;
import bcclass.BCMethod;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.Variable;
import bcexpression.javatype.JavaBasicType;
import bcexpression.jml.OLD;
import constants.BCConstant;
import constants.BCConstantFieldRef;
import constants.BCConstantMethodRef;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;
import formula.QuantifiedFormula;
import formula.atomic.Predicate;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ModifiesDOT extends ModifiesExpression {

	/*private ModifiesExpression modifies;
	private Expression expr;
	*/
	public ModifiesDOT(ModifiesExpression modifiesIdent, Expression expr, BCConstantPool _constantPool) {
		super(modifiesIdent, expr, _constantPool);
	}

	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getCondition()
	 */
	
	
	/**
	 * forall o : Type (Type <: type(ref) ) . o!= ref ==> old(b(o)) == b(o)
	 * where b is the field that is accessed 
	 */
	public Expression getPostCondition() {
/*		Variable o = new Variable(FreshIntGenerator.getInt() );
		Expression ref = getSubExpressions()[0];
		BCConstantFieldRef constantField = fieldAccess.getFieldConstRef();
		Formula condition = null;
		if (ref instanceof ModifiesArrayInterval) {
			ModifiesArrayInterval modifExpr = (ModifiesArrayInterval)ref;
			condition = (Formula)modifExpr.getCondition(o);
		} else {
			condition = new Predicate2Ar(o, ref , PredicateSymbol.NOTEQ );
			
		}
		Predicate2Ar o_eq_old_o = new Predicate2Ar( new FieldAccessExpression(constantField, o ) , new OLD(new FieldAccessExpression(constantField, o )), PredicateSymbol.EQ );
		Formula condition_implies_p =  Formula.getFormula(condition, o_eq_old_o, Connector.IMPLIES );
		Quantificator q = new Quantificator(Quantificator.FORALL, o );
		Formula for_all_o = new QuantifiedFormula(condition_implies_p, q );
		return for_all_o;*/
		return Predicate.TRUE;
	}


	
	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getModifiedExpression()
	 */
	public Expression getExpression() {
		
		BCConstant c = (BCConstant)((ModifiesIdent) getModifies()).getExpression();	
		if (c instanceof BCConstantFieldRef ) {
			FieldAccess fieldAccess = new FieldAccess((BCConstantFieldRef)c , getObjectDereferenced());
			return fieldAccess;
		} 		
		if (c instanceof BCConstantMethodRef) {
		// TODO	
		}
		return null;
		
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		// TODO Auto-generated method stub
		return null;
	}

	 
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = getModifies()  + "( " + getSubExpressions()[1]  + ")"; 
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return null;
	}

}
