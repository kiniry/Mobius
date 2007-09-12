package annot.modifexpression;

import annot.bcclass.BCClass;
import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;

public class ModifiesDOT extends ModifiesExpression {

	public ModifiesDOT(ModifiesExpression modifiesIdent, Expression expr, BCClass _clazz) {
		super(modifiesIdent, expr, _clazz);
	}

//	/* (non-Javadoc)
//	 * @see modifexpression.ModifiesExpression#getPostCondition()
//	 */
//
//	/**
//	 * forall o : Type (Type <: type(ref) ) . o!= ref ==> old(b(o)) == b(o)
//	 * 
//	 * where b is the field that is accessed 
//	 */
//	public Expression getPostCondition(IJml2bConfiguration config, int state) {
//		Expression objDeref = getObjectDereferenced();
//		Expression objDerefDotField = getExpression();
//		
//		Variable obj = new Variable(FreshIntGenerator.getInt(), getType());
//		
//		// the upper limit for the obj type
//		Expression type = getType();
//	
//		//typeof(obj) <: typeof(derefObj)
//		Predicate2Ar objTypeSubTypeOf= new Predicate2Ar( new TYPEOF(obj), type, PredicateSymbol.SUBTYPE);
//		
//		Quantificator q = new Quantificator(Quantificator.FORALL,obj );
//		// obj != objDeref
//		Formula objNotEqobjDeref = Formula.getFormula( new Predicate2Ar( obj, objDeref, PredicateSymbol.EQ), 
//				Connector.NOT);
//		
//		// 
//		Expression objDerefDotcopy = objDerefDotField.copy();
//	
//		Expression objDotField = objDerefDotcopy.generalize(objDeref , obj  );
//		Predicate2Ar objDotFieldEqOldObjDotField ;
//		if (state == ClassStateVector.RETURN_STATE ) {
//			objDotFieldEqOldObjDotField = new Predicate2Ar( objDotField, new OLD(objDotField), PredicateSymbol.EQ);
//		} else {
//			Expression fieldAtState = objDotField.copy().atState(state);
//			objDotFieldEqOldObjDotField = new Predicate2Ar( objDotField, fieldAtState, PredicateSymbol.EQ);
//			
//		}
//	    Formula f = Formula.getFormula( Formula.getFormula( objNotEqobjDeref, objTypeSubTypeOf, Connector.AND ) , objDotFieldEqOldObjDotField, Connector.IMPLIES );
//		f = Formula.getFormula(f, q );
//	    return f;
//	}
//
//	/* (non-Javadoc)
//	 * @see modifexpression.ModifiesExpression#getModifiedExpression()
//	 */
//	public Expression getExpression() {
//		
//		BCConstant c = (BCConstant)((ModifiesIdent) getModifies()).getExpression();	
//		if (c instanceof BCConstantFieldRef ) {
//			FieldAccess fieldAccess = new FieldAccess((BCConstantFieldRef)c , getObjectDereferenced());
//			return fieldAccess;
//		} 		
//		if (c instanceof BCConstantMethodRef) {
//		// TODO	
//		}
//		return null;
//	}

//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#getType()
//	 */
//	public Expression getType() {
//		BCConstantFieldRef constField = (BCConstantFieldRef)getExpressionModifies();
//		JavaType type = JavaType.getJavaType( ((BCConstantClass)clazz.getConstantPool().getConstant(constField.getClassIndex())).getName() );
//		return type;
//	}

	 
	public String printCode1(BMLConfig conf) {
//		String s = getModifies().printCode(conf)  + "( " + getSubExpressions()[1].printCode(conf)  + ")";
		if (getSubExpressions()[1].printCode(conf).equals("this"))
			return getModifies().printCode(conf);
		return getSubExpressions()[1].printCode(conf)+"."+getModifies().printCode(conf);
	}
}
