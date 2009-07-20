/*
 * Created on Sep 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.modifexpression;


import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcclass.ClassStateVector;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.Variable;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.constants.BCConstant;
import bytecode_wp.constants.BCConstantClass;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.constants.BCConstantMethodRef;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.formula.Quantificator;
import bytecode_wp.utils.FreshIntGenerator;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ModifiesDOT extends ModifiesExpression {


	public ModifiesDOT(ModifiesExpression modifiesIdent, Expression expr, BCClass _clazz) {
		super(modifiesIdent, expr, _clazz);
	}

	/* (non-Javadoc)
	 * @see modifexpression.ModifiesExpression#getPostCondition()
	 */

	/**
	 * forall o : Type (Type <: type(ref) ) . o!= ref ==> old(b(o)) == b(o)
	 * 
	 * where b is the field that is accessed 
	 */
	public Expression getPostCondition(IJml2bConfiguration config, int state) {
		Expression objDeref = getObjectDereferenced();
		Expression objDerefDotField = getExpression();
		
		Variable obj = new Variable(FreshIntGenerator.getInt(), getType());
		
		// the upper limit for the obj type
		Expression type = getType();
	
		//typeof(obj) <: typeof(derefObj)
		Predicate2Ar objTypeSubTypeOf= new Predicate2Ar( new TYPEOF(obj), type, PredicateSymbol.SUBTYPE);
		
		Quantificator q = new Quantificator(Quantificator.FORALL,obj );
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
			Expression fieldAtState = objDotField.copy().atState(state);
			objDotFieldEqOldObjDotField = new Predicate2Ar( objDotField, fieldAtState, PredicateSymbol.EQ);
			
		}
	    Formula f = Formula.getFormula( Formula.getFormula( objNotEqobjDeref, objTypeSubTypeOf, Connector.AND ) , objDotFieldEqOldObjDotField, Connector.IMPLIES );
		f = Formula.getFormula(f, q );
	    return f;
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
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		BCConstantFieldRef constField = (BCConstantFieldRef)getExpressionModifies();
		JavaType type = JavaType.getJavaType( ((BCConstantClass)clazz.getConstantPool().getConstant(constField.getClassIndex())).getName() );
		return type;
	}

	 
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = getModifies()  + "( " + getSubExpressions()[1]  + ")"; 
		return s;
	}

}
