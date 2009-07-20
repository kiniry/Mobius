/*
 * Created on Sep 10, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;
import utils.FreshIntGenerator;
import bcclass.BCConstantPool;
import bcclass.ClassStateVector;
import bcexpression.ArrayAccessExpression;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.NumberLiteral;
import bcexpression.QuantifiedExpression;
import bcexpression.Variable;
import bcexpression.javatype.JavaArrType;
import bcexpression.javatype.JavaBasicType;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.JML_CONST_TYPE;
import bcexpression.jml.OLD;
import bcexpression.jml.TYPEOF;
import constants.ArrayLengthConstant;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;
import formula.QuantifiedFormula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ModifiesArray extends ModifiesExpression {
	public ModifiesArray(ModifiesExpression arrayAccess, SpecArray specArray,
			BCConstantPool _constantPool) {
		super(arrayAccess, specArray, _constantPool);
	}
	public SpecArray getSpecArray() {
		return (SpecArray) getSubExpressions()[1];
	}

	/**
	 * @return forall o : ElemType( ). (forall i:int) . (i >= startInterval && i = <
	 *         endInterval) ==>  o != array[i]
	 */
	public Expression getPostCondition(int state) {
		SpecArray specArr = getSpecArray();
		Formula condition = null;
		if (specArr instanceof ArrayElemFromTo) {
			condition = (Formula) getConditionForInterval(state);
			return condition;
		}
		if (specArr instanceof AllArrayElem) {
			condition = (Formula) getConditionForAll(state);
			return condition;
		}
		if (specArr instanceof SingleIndex) {
			condition = (Formula) getConditionForSingleIndice(state);
			return condition;
		}
		return null;
	}
	/**
	 * forall o: Type (Type <: _class) (forall index : 0 <= index <
	 * length(arr(o))) o != arrRef ==> old( arr(o)[index]) == arr'( o)[index]
	 * and forall o: Type (Type <: _class). forall j :int( j!=i ) o == arrRef
	 * ==> arr(o)[j] == arr'(o)[j] s is the all the other fields of arr.
	 * 
	 * @param constantVar
	 * @return
	 */
	
	/**
	 * forall o: Type (Type <: _class) o != arrRef ==> old( arr(o)) == arr( o)
	 * and forall o: Type (Type <: _class). forall j :int( j!=i ) o == arrRef
	 * ==> old( f^s(o)) == f^s( o) s is the all the other fields of arr.
	 * 
	 * @return
	 */
public Expression getConditionForSingleIndice(int state) {
		//		forall o: Type (Type <: _class) o != arrRef ==> old( arr(o)) == arr(
		// o)
		Expression arrayModified = getExpression();
		Expression objDeref = getObjectDereferenced();
		Expression index = ((SingleIndex) getSpecArray()).getIndex();
		//////////////////////////////////////////////////
		Expression _class = getType();
		Variable obj0 = new Variable(FreshIntGenerator.getInt(),  JavaArrType.ARRTYPE);
		Variable i0 = new Variable(FreshIntGenerator.getInt(), 	JavaBasicType.JavaINT);
		Formula o_not_eq_arr_Ref = Formula.getFormula(new Predicate2Ar(obj0, objDeref,
				PredicateSymbol.EQ), Connector.NOT);
		Expression array = arrayModified.copy().substitute(objDeref, obj0);
		//deprecated : new ArrayAccessExpression(new
		// FieldAccess(constantField, obj ), index )
		Predicate2Ar o_not_eq_arr_Ref_implies = new Predicate2Ar(array,
				new OLD(array), PredicateSymbol.EQ);
		Formula domain0 = new Predicate2Ar(obj0.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Formula f = Formula.getFormula(Formula.getFormula(
				        				    new Formula[]{domain0, 
					        		                      o_not_eq_arr_Ref,
										                  new Predicate2Ar(i0, new NumberLiteral(0), PredicateSymbol.GRTEQ) ,
										                  new Predicate2Ar(i0 , new FieldAccess( ArrayLengthConstant.ARRAYLENGTHCONSTANT, obj0 ), PredicateSymbol.LESS )}, 
				                                          Connector.AND),
				                        o_not_eq_arr_Ref_implies, Connector.IMPLIES);
		
		Quantificator q1 = new Quantificator(Quantificator.FORALL, new Variable[]{ i0, obj0 });
		//forall o: Type (Type <: _class  and  o != arrRef) ==> old( arr(o)) == arr( o)
		
	    Formula qf = Formula.getFormula( f , q1);
		
	    ////////////END OF FIRST CONJUNCT
	    ///////////////////////////////////////
		///////////////////////////////////////////////////////////////
		//////////////////////////////////////
		/////////////////////////////////////////
		///forall ( o: Type, j :int) .( Type <: _class) &&  ( j!=i ) && ( o == arrRef ) ==> old( f^s(o)) == f^s( o)
		//  s is the all the other fields of arr.
		////////////////////////////////////
	    
		// o == arrRef
		Predicate2Ar o_eq_arr_Ref = new Predicate2Ar(obj0, objDeref,
				PredicateSymbol.EQ);
	
		// so obj2 is of a type gama i.e. still not known
		Variable obj2 = new Variable(FreshIntGenerator.getInt(), JavaArrType.ARRTYPE);
		//		 obj2 == arrRef
		Predicate2Ar obj2_eq_arrRef = new Predicate2Ar(obj2, objDeref,
				PredicateSymbol.EQ);
		// forall i:int. ( i != index)
		Variable i = new Variable(FreshIntGenerator.getInt(),
				JavaBasicType.JavaINT);
		/*Formula domain2 = new Predicate2Ar(i, index, PredicateSymbol.NOTEQ);*/
		Quantificator q2 = new Quantificator(Quantificator.FORALL, new Variable[]{obj2, i});
		
		// arr(obj2, i) == old(arr(obj2, i) )
		Expression thisArray = arrayModified.copy().substitute(objDeref, obj0);
		thisArray = thisArray.generalize(index, i);
		Predicate2Ar f2;
		if (state == ClassStateVector.RETURN_STATE) {
				f2 = new Predicate2Ar(thisArray, new OLD(thisArray),
				PredicateSymbol.EQ);
		} else {
			Expression arrAtState = thisArray.copy().atState(state);
			f2 = new Predicate2Ar(thisArray, arrAtState,
					PredicateSymbol.EQ);
		}
		// e <: type(this) && i != index && e == this ==> e[i] =old(e[i])  
		Formula domain = Formula.getFormula( new Formula[]{ new Predicate2Ar(obj2.getType(), _class, PredicateSymbol.SUBTYPE), 
											                Formula.getFormula( new Predicate2Ar(i, index, PredicateSymbol.EQ), Connector.NOT) , 
											                new Predicate2Ar(i, new NumberLiteral(0), PredicateSymbol.GRTEQ) ,
											                new Predicate2Ar(i, new FieldAccess(ArrayLengthConstant.ARRAYLENGTHCONSTANT, obj2 ), PredicateSymbol.LESS) ,
															obj2_eq_arrRef}, 
											  Connector.AND );
		Formula anotherArrayEqArrayModif = Formula.getFormula( domain, f2, Connector.IMPLIES );
		
		
		Formula anotherArrayEqArrayModifForAll = Formula.getFormula( anotherArrayEqArrayModif ,
				q2);
		///////////////////////////
		Formula formula = Formula.getFormula(qf,
				anotherArrayEqArrayModifForAll, Connector.AND);
		return formula;
	}	

	
	/**
	 * modifies ref.a[i1..i2] forall o:Type (Type <: type(this) ) o != ref ==>
	 * forall i :int.( i1= < i <i2). o.a[i] == old(o.a[i])
	 * 
	 * and forall o:Type (Type <: type(this) ) o == ref ==> forall i :int.( i1 >
	 * i and i > i2). o.a[i] == old(o.a[i])
	 * 
	 * @param ind1
	 * @param ind2
	 * @return
	 */
	public Expression getConditionForInterval(int state) {
		Expression ind1 = ((ArrayElemFromTo) getSpecArray()).getStart();
		Expression ind2 = ((ArrayElemFromTo) getSpecArray()).getEnd();
		// forall i :int( i1=< i <i2). ref.a[i]
		QuantifiedExpression arrayModified = (QuantifiedExpression) getExpression();
		//ref.a[i]
		Expression quantifiedExpression = arrayModified
				.getTheExpressionQuantified();
		//ref
		Expression objDeref = getObjectDereferenced();
		Expression _class = getType();
		///////////
		/*
		 * Variable obj1 = new Variable(FreshIntGenerator.getInt(),
		 * JavaReferenceType.ReferenceType);
		 */
		Variable obj1 = new Variable(FreshIntGenerator.getInt(), JavaArrType.ARRTYPE);
		Formula obj_not_eq_arr_Ref = Formula.getFormula( new Predicate2Ar(obj1, objDeref,
				PredicateSymbol.EQ), Connector.NOT);
		// (ref.a[i]).generalise(ref, obj) = obj.a[i]
		Expression objArr = quantifiedExpression.copy();
		objArr = objArr.generalize(objDeref, obj1);
		//variable that represents the index of the array
		Variable varIndex = (Variable) arrayModified.getQuantificator().getBoundVars()[0];
		Quantificator quantificators = new Quantificator(Quantificator.FORALL,
				new Variable[]{obj1, varIndex});
		// obj.a[ i ] == old(obj.a[ i ] )
		Predicate2Ar obj_arr_i1_i2 ;
		if ( state == ClassStateVector.RETURN_STATE) {
			obj_arr_i1_i2 = new Predicate2Ar(objArr, new OLD(objArr),
				PredicateSymbol.EQ);
		} else {
			Expression arrAtState = objArr.copy().atState(state);
			obj_arr_i1_i2 = new Predicate2Ar(objArr, arrAtState,
					PredicateSymbol.EQ);
		}
		Formula domain1 = new Predicate2Ar(obj1.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Formula quantify_obj_arr_i1_i2 = 
										Formula.getFormula(Formula.getFormula( new Formula[]{ new Predicate2Ar(varIndex,
																			  new NumberLiteral(0), 
																			  PredicateSymbol.GRTEQ),
				                                           new Predicate2Ar(varIndex, new FieldAccess(
				                                           			                           ArrayLengthConstant.ARRAYLENGTHCONSTANT, objArr
								                                                               .getSubExpressions()[0].copy()),
						                                                                       PredicateSymbol.LESS),
															domain1,
															obj_not_eq_arr_Ref}, 
														   Connector.AND), obj_arr_i1_i2, Connector.IMPLIES);
		/*Formula obj_not_eq_implies = Formula.getFormula(obj_not_eq_arr_Ref,
				quantify_obj_arr_i1_i2, Connector.IMPLIES);*/
		
		/*Quantificator q1 = new Quantificator(Quantificator.FORALL, obj1);*/
		/*
		 * forall o:Type (Type <: type(this) ) o != ref ==> forall i :int.( 0 = <
		 * i < o.a.length ). o.a[i] == old(o.a[i])
		 */
		Formula obj_not_eq_implies_quantify = Formula.getFormula(
				Formula.getFormula(domain1, quantify_obj_arr_i1_i2, Connector.IMPLIES), quantificators);
		//////////////////////////////////////////////////////////////////////////////////////////////////////////////
		/////////////////////////////////////in case the referece is equal to
		// this reference then all the array elemnts
		//////////////////////////////out of the index interval specified
		// should not change///////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////
		/*
		 * Variable obj2 = new Variable(FreshIntGenerator.getInt(),
		 * JavaReferenceType.ReferenceType);
		 */
		Variable obj2 = new Variable(FreshIntGenerator.getInt(), JavaArrType.ARRTYPE);
		Predicate2Ar obj2_eq_arr_Ref = new Predicate2Ar(obj2, objDeref,
				PredicateSymbol.EQ);
		Variable i = new Variable(FreshIntGenerator.getInt(), JavaType.JavaINT);
		Predicate2Ar i_less_ind1 = new Predicate2Ar(i, ind1,
				PredicateSymbol.LESS);
		Predicate2Ar i_grte_0 = new Predicate2Ar(i, new NumberLiteral(0),
				PredicateSymbol.GRTEQ);
		Predicate2Ar i_grt_ind2 = new Predicate2Ar(i, ind2, PredicateSymbol.GRT);
		Expression arrLength = new FieldAccess(
				ArrayLengthConstant.ARRAYLENGTHCONSTANT, getModifies()
						.getExpression());
		Predicate2Ar i_leq_arr_length = new Predicate2Ar(i, arrLength,
				PredicateSymbol.LESS);
		Formula domain2 = Formula
				.getFormula(i_leq_arr_length, Formula.getFormula(i_grt_ind2,
						Formula
								.getFormula(i_less_ind1, i_grte_0,
										Connector.AND), Connector.AND),
						Connector.AND);
	
		
		Expression _v = arrayModified.getQuantificator().getBoundVars()[0];
		Expression array = quantifiedExpression.copy().substitute(objDeref,
				obj2);
		array = array.substitute(_v, i);
		Predicate2Ar this_arr_out_of_interval_unchanged;
		if (state == ClassStateVector.RETURN_STATE) {
			this_arr_out_of_interval_unchanged = new Predicate2Ar(array,
					new OLD(array), PredicateSymbol.EQ);
		} else {
			Expression arrayAtState = array.copy().atState(state);
			this_arr_out_of_interval_unchanged = new Predicate2Ar(array,
					arrayAtState, PredicateSymbol.EQ);
		}
		Quantificator quantificators2 = new Quantificator(Quantificator.FORALL, new Variable[]{(Variable)arrayModified.getQuantificator().getBoundVars()[0],  i, obj2});
/*		Formula obj2_eq_impl = Formula.getFormula(
				Formula.getFormula(domain2, this_arr_out_of_interval_unchanged, 
						Connector.IMPLIES ), quantificators2);*/
		Formula domain3 = new Predicate2Ar(obj2.getType(), _class,
				PredicateSymbol.SUBTYPE);
		/*Quantificator q3 = new Quantificator(Quantificator.FORALL, obj2);*/
		Formula obj2_eq_impl_quantify = new QuantifiedFormula(Formula
				.getFormula(Formula.getFormula(new Formula[]{obj2_eq_arr_Ref, domain2, domain3}, Connector.AND ), 
						   this_arr_out_of_interval_unchanged, Connector.IMPLIES),
				quantificators2);
		Formula f = Formula.getFormula(obj_not_eq_implies_quantify,
				obj2_eq_impl_quantify, Connector.AND);
		return f;
	}
	/**
	 * @param constantVar
	 * @return
	 */
	/*
	 * private Formula getConditionForAllCalled(ValueOfConstantAtState
	 * constantVar) {
	 * 
	 * Expression array = getModifies().getExpression(); Expression ind1 = new
	 * NumberLiteral( 0); Expression ind2 = new
	 * FieldAccess(ArrayLengthConstant.ARRAYLENGTHCONSTANT, array ); // forall
	 * i :int( i1= < i <i2). ref.a[i] QuantifiedExpression arrayModified =
	 * (QuantifiedExpression) getExpression(); //ref.a[i] Expression
	 * quantifiedExpression = arrayModified .getQuantifiedExpression();
	 * Quantificator[] quantificators = arrayModified.getQuantificator(); //ref
	 * Expression objDeref = getObjectDereferenced(); Expression _class =
	 * getType();
	 * 
	 * /////////// Variable obj1 = new Variable(FreshIntGenerator.getInt(), new
	 * Variable( FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
	 * Predicate2Ar obj_not_eq_arr_Ref = new Predicate2Ar(obj1, objDeref,
	 * PredicateSymbol.NOTEQ); // (ref.a[i]).generalise(ref, obj) = obj.a[i]
	 * Expression objArr = quantifiedExpression.copy(); objArr =
	 * objArr.generalize(objDeref, obj1);
	 *  // obj.a[ i ] == old(obj.a[ i ] ) Expression objArrPrim =
	 * objArr.copy(); objArrPrim = objArrPrim.substitute(getConstantFieldRef(),
	 * constantVar); Predicate2Ar obj_arr_i1_i2 = new Predicate2Ar(objArr,
	 * objArrPrim, PredicateSymbol.EQ ); Formula quantify_obj_arr_i1_i2 = new
	 * QuantifiedFormula( obj_arr_i1_i2 , quantificators);
	 * 
	 * Formula obj_not_eq_implies = Formula.getFormula( obj_not_eq_arr_Ref,
	 * quantify_obj_arr_i1_i2, Connector.IMPLIES);
	 * 
	 * Formula domain1 = new Predicate2Ar(obj1.getType(), _class,
	 * PredicateSymbol.SUBTYPE); Quantificator q1 = new
	 * Quantificator(Quantificator.FORALL, obj1, domain1);
	 * 
	 * 
	 * forall o:Type (Type <: type(this) ) o != ref ==> forall i :int.( i1= < i
	 * <i2). o.a[i] == old(o.a[i])
	 * 
	 * 
	 * Formula obj_not_eq_implies_quantify =
	 * Formula.getFormula(obj_not_eq_implies, q1 );
	 * 
	 * 
	 * return obj_not_eq_implies_quantify;
	 */
	/**
	 * forall o : T (T <: typeof( ref)) forall index :( 0 <= index <
	 * length(array)) o != ref => o.arr[i] = old( o.arr[i] )
	 * 
	 * @param o
	 * @return
	 */
	public Expression getConditionForAll(int state) {
		Expression array = getModifies().getExpression();
		Expression ind1 = new NumberLiteral(0);
		Expression ind2 = new FieldAccess(
				ArrayLengthConstant.ARRAYLENGTHCONSTANT, array);
		// forall i :int( i1=< i <i2). ref.a[i]
		QuantifiedExpression arrayModified = (QuantifiedExpression) getExpression();
		//ref.a[i]
		Expression quantifiedExpression = arrayModified
				.getTheExpressionQuantified();
		Quantificator quantificators = arrayModified.getQuantificator();
		//ref
		Expression objDeref = getObjectDereferenced();
		Expression _class = getType();
		///////////
		Variable obj1 = new Variable(FreshIntGenerator.getInt(), JavaArrType.ARRTYPE);
		Formula obj_not_eq_arr_Ref = Formula.getFormula( new Predicate2Ar(obj1, objDeref,
				PredicateSymbol.EQ), Connector.NOT);
		// (ref.a[i]).generalise(ref, obj) = obj.a[i]
		Expression objArr = quantifiedExpression.copy();
		objArr = objArr.generalize(objDeref, obj1);
		Predicate2Ar obj_arr_i1_i2;
		// obj.a[ i ] == old(obj.a[ i ] )
		if (state == ClassStateVector.RETURN_STATE) {
			obj_arr_i1_i2 = new Predicate2Ar(objArr, new OLD(objArr),
					PredicateSymbol.EQ);
		} else {
			Expression arrAtState = objArr.copy().atState(state);
			obj_arr_i1_i2 = new Predicate2Ar(objArr, arrAtState,
					PredicateSymbol.EQ);
		}
		Formula quantify_obj_arr_i1_i2 = new QuantifiedFormula(obj_arr_i1_i2,
				quantificators);
		Formula obj_not_eq_implies = Formula.getFormula(obj_not_eq_arr_Ref,
				quantify_obj_arr_i1_i2, Connector.IMPLIES);
		Formula domain1 = new Predicate2Ar(new TYPEOF(obj1), _class,
				PredicateSymbol.SUBTYPE);
		Quantificator q1 = new Quantificator(Quantificator.FORALL, obj1);
		/*
		 * forall o:Type (Type <: type(this) ) o != ref ==> forall i :int.( i1= <
		 * i <i2). o.a[i] == old(o.a[i])
		 *  
		 */
		Formula obj_not_eq_implies_quantify = Formula.getFormula(
				Formula.getFormula(domain1, obj_not_eq_implies, Connector.IMPLIES ), q1);
		return obj_not_eq_implies_quantify;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see modifexpression.ModifiesExpression#getModifiedExpression()
	 */
	public Expression getExpression() {
		SpecArray specArray = getSpecArray();
		Expression modExpr = getModifies().getExpression();
		//a[i]
		if (specArray instanceof SingleIndex) {
			// return a[ind]
			Expression index = ((SingleIndex) specArray).getIndex();
			Expression array = getModifies().getExpression();
			ArrayAccessExpression arrayAccess = new ArrayAccessExpression(
					array, index);
			return arrayAccess;
		}
		Expression start = null;
		Expression end = null;
		Predicate2Ar i_greq_start = null;
		Predicate2Ar i_le_end = null;
		Variable i = new Variable(FreshIntGenerator.getInt(), JavaType.JavaINT);
		// forall 0 =< i < a.length . a[i]
		if (specArray instanceof AllArrayElem) {
			//			 return forall i. start =< i <= end a[i]
			start = new NumberLiteral(0);
			end = new FieldAccess(ArrayLengthConstant.ARRAYLENGTHCONSTANT,
					modExpr);
			i_greq_start = new Predicate2Ar(i, start, PredicateSymbol.GRTEQ);
			i_le_end = new Predicate2Ar(i, end, PredicateSymbol.LESS);
		}
		//		 forall start =< i < end . a[i]
		if (specArray instanceof ArrayElemFromTo) {
			// return forall i. start =< i <= end a[i]
			start = ((ArrayElemFromTo) specArray).getStart();
			end = ((ArrayElemFromTo) specArray).getEnd();
			i_greq_start = new Predicate2Ar(i, start, PredicateSymbol.GRTEQ);
			i_le_end = new Predicate2Ar(i, end, PredicateSymbol.LESSEQ);
		}
		Formula domain = Formula.getFormula(i_greq_start, i_le_end,
				Connector.AND);
		Quantificator q = new Quantificator(Quantificator.FORALL, i);
		QuantifiedExpression f = new QuantifiedExpression(  q, domain,
				new ArrayAccessExpression(modExpr, i));
		return f;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = getModifies().toString() + " [" + getSpecArray() + "]";
		return s;
	}
}
