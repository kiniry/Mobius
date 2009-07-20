/*
 * Created on Sep 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.modifexpression;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.formula.Predicate0Ar;

/**
 * @author mpavlova
 *
 * 
 */
public class ModifiesIdent extends ModifiesExpression {
	
	public ModifiesIdent(Expression  ident, BCClass _clazz) {
		super(ident , _clazz);
	}

	/**
	 * this method overrides a method from the super class ModifiesExpression 
	 * It is called when a static field is modified
	 */
	public Expression getPostCondition(IJml2bConfiguration config, int state) {
			//when the modification is assumed then the condition is TRUE
			// when the modification is proven then 			
		     return Predicate0Ar.TRUE;
			/*BCConstantFieldRef  objDerefDotField = (BCConstantFieldRef )getExpression();
		
			JavaReferenceType classWhereDecl = objDerefDotField.getClassWhereDeclared();
			
			FieldAccess staticFieldAc = new FieldAccess(objDerefDotField );
			Predicate2Ar fieldAtStateEq = null;
			if (state == ClassStateVector.RETURN_STATE ) {
				fieldAtStateEq = new Predicate2Ar( staticFieldAc, new OLD(staticFieldAc), PredicateSymbol.EQ);
			} else {
				Expression fieldAtState = staticFieldAc.copy();
				fieldAtState = fieldAtState.atState( state);
				fieldAtStateEq = new Predicate2Ar( staticFieldAc , fieldAtState, PredicateSymbol.EQ);
				
			}
		   	return fieldAtStateEq;*/
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
