/*
 * Created on Sep 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;


import utils.FreshIntGenerator;
import bcclass.BCConstantPool;
import bcclass.ClassStateVector;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.Variable;
import bcexpression.javatype.JavaType;
import bcexpression.jml.OLD;
import bcexpression.jml.TYPEOF;
import constants.BCConstant;
import constants.BCConstantClass;
import constants.BCConstantFieldRef;
import constants.BCConstantMethodRef;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ModifiesDOT extends ModifiesExpression {


	public ModifiesDOT(ModifiesExpression modifiesIdent, Expression expr, BCConstantPool _constantPool) {
		super(modifiesIdent, expr, _constantPool);
	}

	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getPostCondition()
	 */

	/**
	 * forall o : Type (Type <: type(ref) ) . o!= ref ==> old(b(o)) == b(o)
	 * 
	 * where b is the field that is accessed 
	 */
	public Expression getPostCondition(int state) {
		Expression objDeref = getObjectDereferenced();
		Expression objDerefDotField = getExpression();
		
		Variable obj = new Variable(FreshIntGenerator.getInt());
		// the upper limit for the obj type
		Expression type = objDeref.getType();
		
/*		
		BCConstantFieldRef constField = (BCConstantFieldRef)getConstantFieldRef();
		Expression type  = */
		
		//typeof(obj) <: typeof(derefObj)
		Predicate2Ar objTypeSubTypeOf= new Predicate2Ar( new TYPEOF(obj), type, PredicateSymbol.SUBTYPE);
		
		// obj != objDeref
		Formula objNotEqobjDeref = Formula.getFormula( new Predicate2Ar( obj, objDeref, PredicateSymbol.EQ), 
				Connector.NOT);
		
		// 
		Expression objDerefDotcopy = objDerefDotField.copy();
	
		Expression objDotField = objDerefDotcopy.generalize(objDeref , obj  );
		Predicate2Ar objDotFieldEqOldObjDotField ;
		if (state == ClassStateVector.RETURN_STATE ) {
			objDotFieldEqOldObjDotField = new Predicate2Ar( objDotField, new OLD(objDotField), PredicateSymbol.EQ);
		} else {
			Expression fieldAtState = objDotField.copy().atState( state);
			objDotFieldEqOldObjDotField = new Predicate2Ar( objDotField, fieldAtState, PredicateSymbol.EQ);
			
		}
		/*Formula f = Formula.getFormula(objNotEqobjDeref, objDotFieldEqOldObjDotField, Connector.IMPLIES );*/
		/*Formula f = Formula.getFormula( Formula.getFormula( Formula.getFormula( objNotEqobjDeref, objTypeSubTypeOf, Connector.AND ) , objDotFieldEqOldObjDotField, Connector.IMPLIES ), new Quantificator(Quantificator.FORALL, obj));
*/		Formula f = Formula.getFormula( Formula.getFormula( objNotEqobjDeref, objTypeSubTypeOf, Connector.AND ) , objDotFieldEqOldObjDotField, Connector.IMPLIES );
		return f;
	}


	/**
	 * 
	 * @param constantVar
	 * @return the postcondition for invokations of the method that contains this modifies clause
	 *//*
	public Expression getPostConditionWhenCalled(ValueOfConstantAtState constantVar) {
		Expression objDeref = getObjectDereferenced();
		Expression objDerefDotField = getExpression();
		
		Variable obj = new Variable(FreshIntGenerator.getInt());
		// the upper limit for the obj type
		Expression type = objDeref.getType();

		//typeof(obj) <: typeof(derefObj)
		Predicate2Ar objTypeSubTypeOf= new Predicate2Ar( new TYPEOF(obj), type, PredicateSymbol.SUBTYPE);
		
		// obj != objDeref
		Predicate2Ar objNotEqobjDeref = new Predicate2Ar( obj, objDeref, PredicateSymbol.NOTEQ);
		
		// 
		Expression objDerefDotcopy = objDerefDotField.copy();
	
		Expression objDotField = objDerefDotcopy.generalize(objDeref , obj  );
		
		Expression objDotFieldPrim = objDotField.copy();
		objDotFieldPrim = objDotFieldPrim.substitute(getConstantFieldRef() , constantVar  );
		
		Predicate2Ar objDotFieldEqOldObjDotField = new Predicate2Ar( objDotField, objDotFieldPrim, PredicateSymbol.EQ);
		
		Formula f = Formula.getFormula(objNotEqobjDeref, objDotFieldEqOldObjDotField, Connector.IMPLIES );
		f = Formula.getFormula( f, new Quantificator(Quantificator.FORALL, obj, objTypeSubTypeOf ));
		return f;
	}
*/
	
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
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		BCConstantFieldRef constField = (BCConstantFieldRef)getConstantFieldRef();
		JavaType type = JavaType.getJavaType( ((BCConstantClass)constantPool.getConstant(constField.getClassIndex())).getName() );
		return type;
	}

	 
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = getModifies()  + "( " + getSubExpressions()[1]  + ")"; 
		return null;
	}




}
