/*
 * Created on Sep 10, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;
import constants.ArrayLengthConstant;
import utils.FreshIntGenerator;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;
import formula.QuantifiedFormula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;
import bcclass.BCConstantPool;
import bcclass.ClassStateVector;
import bcexpression.ArrayAccessExpression;
import bcexpression.ValueOfConstantAtState;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.NumberLiteral;
import bcexpression.QuantifiedExpression;
import bcexpression.QuantifiedExpression;
import bcexpression.Variable;
import bcexpression.javatype.JavaArrType;
import bcexpression.javatype.JavaBasicType;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.JML_CONST_TYPE;
import bcexpression.jml.OLD;
import bcexpression.jml.TYPEOF;
import bcexpression.vm.Stack;
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
	 * @return forall o : ElemType( ). forall i:int . (i >= startInterval && i = <
	 *         endInterval) . o != array[i]
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
	/*
	 * public Expression
	 * getConditionForSingleIndiceCalled(ValueOfConstantAtState constantVar) { //
	 * forall o: Type (Type <: _class) o != arrRef ==> old( arr(o)) == arr( // o)
	 * Expression arrayModified = getExpression(); Expression objDeref =
	 * getObjectDereferenced(); Expression index = ((SingleIndex)
	 * getSpecArray()).getIndex();
	 * ////////////////////////////////////////////////// Expression _class =
	 * getType(); Variable obj = new Variable(FreshIntGenerator.getInt(), new
	 * Variable( FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
	 * Predicate2Ar o_not_eq_arr_Ref = new Predicate2Ar(obj, objDeref,
	 * PredicateSymbol.NOTEQ); Expression array =
	 * arrayModified.copy().substitute(objDeref, obj); //deprecated : new
	 * ArrayAccessExpression(new // FieldAccess(constantField, obj ), index )
	 * 
	 * Expression arrayPrim = array.copy(); arrayPrim = arrayPrim.substitute(
	 * getConstantFieldRef(), constantVar );
	 * 
	 * Predicate2Ar o_not_eq_arr_Ref_implies = new Predicate2Ar(array,
	 * arrayPrim , PredicateSymbol.EQ);
	 * 
	 * 
	 * Formula f = Formula.getFormula(o_not_eq_arr_Ref,
	 * o_not_eq_arr_Ref_implies, Connector.IMPLIES); Formula domain1 = new
	 * Predicate2Ar(obj.getType(), _class, PredicateSymbol.SUBTYPE);
	 * Quantificator q1 = new Quantificator(Quantificator.FORALL, obj,
	 * domain1); //forall o: Type (Type <: _class) o != arrRef ==> old( arr(o)) ==
	 * arr( // o) Formula qf = Formula.getFormula(f, q1);
	 * 
	 * /////////////////////////////////////////////////////////////// // o ==
	 * arrRef Predicate2Ar o_eq_arr_Ref = new Predicate2Ar(obj, objDeref,
	 * PredicateSymbol.EQ); //////////////////////////////////////
	 * ///////////////////////////////////////// ///forall o: Type (Type <:
	 * _class). forall j :int( j!=i ) o == arrRef // ==> old( f^s(o)) == f^s( o) //
	 * s is the all the other fields of arr.
	 * //////////////////////////////////// // so obj2 is of a type gama i.e.
	 * still not known Variable obj2 = new Variable(FreshIntGenerator.getInt(),
	 * new Variable( FreshIntGenerator.getInt(),
	 * JML_CONST_TYPE.JML_CONST_TYPE)); // obj2 == arrRef Predicate2Ar
	 * obj2_eq_arrRef = new Predicate2Ar(obj2, objDeref, PredicateSymbol.EQ); //
	 * forall i:int. ( i != index) Variable i = new
	 * Variable(FreshIntGenerator.getInt(), JavaBasicType.JavaINT); Formula
	 * domain2 = new Predicate2Ar(i, index, PredicateSymbol.NOTEQ);
	 * Quantificator q2 = new Quantificator(Quantificator.FORALL, i, domain2); //
	 * arr(obj2, i) == old(arr(obj2, i) ) Expression thisArray =
	 * arrayModified.copy().substitute(objDeref, obj); thisArray =
	 * thisArray.generalize(index, i);
	 * 
	 * Expression arrayPrim2 = thisArray.copy(); arrayPrim2 =
	 * arrayPrim2.substitute( getConstantFieldRef(), constantVar );
	 * 
	 * Predicate2Ar f2 = new Predicate2Ar(thisArray, arrayPrim2,
	 * PredicateSymbol.EQ); Formula qf2 = Formula.getFormula(f2, q2); //obj2 ==
	 * arrRef ==> forall i:int. ( i != index) qf2 =
	 * Formula.getFormula(obj2_eq_arrRef, qf2, Connector.IMPLIES); Formula
	 * domain3 = new Predicate2Ar(obj2.getType(), _class,
	 * PredicateSymbol.SUBTYPE); Quantificator q3 = new
	 * Quantificator(Quantificator.FORALL, obj2, domain3); // forall obj : T.(T >:
	 * type(arrRef)) obj2 == arrRef ==> forall i:int. // ( i != index) Formula
	 * for_all_obj2_eq_arrRef_implies_no_mod = Formula.getFormula(qf2, q3);
	 * /////////////////////////// Formula formula = Formula.getFormula(qf,
	 * for_all_obj2_eq_arrRef_implies_no_mod, Connector.AND); return formula;
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
		Variable obj = new Variable(FreshIntGenerator.getInt(), new Variable(
				FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
		Predicate2Ar o_not_eq_arr_Ref = new Predicate2Ar(obj, objDeref,
				PredicateSymbol.NOTEQ);
		Expression array = arrayModified.copy().substitute(objDeref, obj);
		//deprecated : new ArrayAccessExpression(new
		// FieldAccess(constantField, obj ), index )
		Predicate2Ar o_not_eq_arr_Ref_implies = new Predicate2Ar(array,
				new OLD(array), PredicateSymbol.EQ);
		Formula f = Formula.getFormula(o_not_eq_arr_Ref,
				o_not_eq_arr_Ref_implies, Connector.IMPLIES);
		Formula domain1 = new Predicate2Ar(obj.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Quantificator q1 = new Quantificator(Quantificator.FORALL, obj, domain1);
		//forall o: Type (Type <: _class) o != arrRef ==> old( arr(o)) == arr(
		// o)
		Formula qf = Formula.getFormula(f, q1);
		
		///////////////////////////////////////////////////////////////
		// o == arrRef
		Predicate2Ar o_eq_arr_Ref = new Predicate2Ar(obj, objDeref,
				PredicateSymbol.EQ);
		//////////////////////////////////////
		/////////////////////////////////////////
		///forall o: Type (Type <: _class). forall j :int( j!=i ) o == arrRef
		// ==> old( f^s(o)) == f^s( o)
		//  s is the all the other fields of arr.
		////////////////////////////////////
		// so obj2 is of a type gama i.e. still not known
		Variable obj2 = new Variable(FreshIntGenerator.getInt(), JavaReferenceType.ReferenceType);
		//		 obj2 == arrRef
		Predicate2Ar obj2_eq_arrRef = new Predicate2Ar(obj2, objDeref,
				PredicateSymbol.EQ);
		// forall i:int. ( i != index)
		Variable i = new Variable(FreshIntGenerator.getInt(),
				JavaBasicType.JavaINT);
		Formula domain2 = new Predicate2Ar(i, index, PredicateSymbol.NOTEQ);
		Quantificator q2 = new Quantificator(Quantificator.FORALL, i, domain2);
		// arr(obj2, i) == old(arr(obj2, i) )
		Expression thisArray = arrayModified.copy().substitute(objDeref, obj);
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
		Formula qf2 = Formula.getFormula(f2, q2);
		//obj2 == arrRef ==> forall i:int. ( i != index)
		qf2 = Formula.getFormula(obj2_eq_arrRef, qf2, Connector.IMPLIES);
		Formula domain3 = new Predicate2Ar(obj2.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Quantificator q3 = new Quantificator(Quantificator.FORALL, obj2,
				domain3);
		//		forall obj : T.(T >: type(arrRef)) obj2 == arrRef ==> forall i:int.
		// ( i != index)
		Formula for_all_obj2_eq_arrRef_implies_no_mod = Formula.getFormula(qf2,
				q3);
		///////////////////////////
		Formula formula = Formula.getFormula(qf,
				for_all_obj2_eq_arrRef_implies_no_mod, Connector.AND);
		return formula;
	}	/**
		  * @param constantVar
		  * @return
		  */
	/*
	 * private Formula getConditionForIntervalCalled(ValueOfConstantAtState
	 * constantVar) { Expression ind1 =
	 * ((ArrayElemFromTo)getSpecArray()).getStart(); Expression ind2 =
	 * ((ArrayElemFromTo)getSpecArray()).getEnd(); // forall i :int( i1= < i
	 * <i2). ref.a[i] QuantifiedExpression arrayModified =
	 * (QuantifiedExpression) getExpression(); //ref.a[i] Expression
	 * quantifiedExpression = arrayModified .getQuantifiedExpression();
	 * 
	 * //ref Expression objDeref = getObjectDereferenced(); Expression _class =
	 * getType();
	 * 
	 * /////////// Variable obj1 = new Variable(FreshIntGenerator.getInt(), new
	 * Variable( FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
	 * Predicate2Ar obj_not_eq_arr_Ref = new Predicate2Ar(obj1, objDeref,
	 * PredicateSymbol.NOTEQ); // (ref.a[i]).generalise(ref, obj) = obj.a[i]
	 * Expression objArr = quantifiedExpression.copy(); objArr =
	 * objArr.generalize(objDeref, obj1);
	 * 
	 * Expression objArrPrim = objArr.copy(); objArrPrim =
	 * objArrPrim.substitute(getConstantFieldRef() , constantVar );
	 *  // obj.a[ i ] == old(obj.a[ i ] ) Predicate2Ar obj_arr_i1_i2 = new
	 * Predicate2Ar(objArr, objArrPrim, PredicateSymbol.EQ );
	 * 
	 * Variable varIndex =
	 * (Variable)arrayModified.getQuantificator()[0].getBoundVar();
	 * Quantificator quantificators = new Quantificator(Quantificator.FORALL,
	 * varIndex, Formula.getFormula(new Predicate2Ar(varIndex, new
	 * NumberLiteral(0),PredicateSymbol.GRTEQ), new Predicate2Ar(varIndex, new
	 * FieldAccess( ArrayLengthConstant.ARRAYLENGTHCONSTANT
	 * ,objArr.getSubExpressions()[0].copy() ) , PredicateSymbol.LESS) ,
	 * Connector.AND )); Formula quantify_obj_arr_i1_i2 = new
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
	 * //////////////////////////////////////////////////////////////////////////////////////////////////////////////
	 * //////////////////////////////////////////////////////////////////////////////////////////////////////////////
	 * ////////////////////////////////////////////////////////////////////////////////////////
	 * Variable obj2 = new Variable(FreshIntGenerator.getInt(), new Variable(
	 * FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
	 * Predicate2Ar obj2_eq_arr_Ref = new Predicate2Ar(obj2, objDeref,
	 * PredicateSymbol.EQ);
	 * 
	 * Variable i = new Variable(FreshIntGenerator.getInt(), JavaType.JavaINT);
	 * 
	 * Predicate2Ar i_less_ind1 = new Predicate2Ar(i, ind1,
	 * PredicateSymbol.LESS ); Predicate2Ar i_grte_0 = new Predicate2Ar(i, new
	 * NumberLiteral(0), PredicateSymbol.GRTEQ); Predicate2Ar i_grt_ind2 = new
	 * Predicate2Ar(i, ind2, PredicateSymbol.GRT); Expression arrLength = new
	 * FieldAccess( ArrayLengthConstant.ARRAYLENGTHCONSTANT,
	 * getModifies().getExpression()); Predicate2Ar i_leq_arr_length = new
	 * Predicate2Ar(i, arrLength, PredicateSymbol.LESS);
	 * 
	 * Formula domain2 = Formula.getFormula(i_leq_arr_length,
	 * Formula.getFormula(i_grt_ind2, Formula.getFormula( i_less_ind1,
	 * i_grte_0, Connector.AND ) , Connector.AND) , Connector.AND);
	 * 
	 * 
	 * Quantificator[] quantificators2 = new
	 * Quantificator[arrayModified.getQuantificator().length];
	 * System.arraycopy(arrayModified.getQuantificator() , 0, quantificators2, 0,
	 * quantificators2.length); Expression _v =
	 * quantificators2[0].getBoundVar(); Expression array =
	 * quantifiedExpression.copy().substitute(objDeref, obj2); array =
	 * array.substitute(_v, i);
	 * 
	 * Expression objArrPrim2 = array.copy(); objArrPrim2 =
	 * objArrPrim2.substitute(getConstantFieldRef() , constantVar );
	 * 
	 * Predicate2Ar this_arr_out_of_interval_unchanged = new Predicate2Ar(
	 * array, objArrPrim2, PredicateSymbol.EQ); quantificators2[0] = new
	 * Quantificator(Quantificator.FORALL, i, domain2 );
	 * 
	 * Formula obj2_eq_impl =
	 * Formula.getFormula(this_arr_out_of_interval_unchanged, quantificators2);
	 * Formula domain3 = new Predicate2Ar(obj2.getType(), _class,
	 * PredicateSymbol.SUBTYPE); Quantificator q3 = new
	 * Quantificator(Quantificator.FORALL, obj2, domain3); Formula
	 * obj2_eq_impl_quantify = new
	 * QuantifiedFormula(Formula.getFormula(obj2_eq_arr_Ref, obj2_eq_impl,
	 * Connector.IMPLIES ), q3 );
	 * 
	 * Formula f = Formula.getFormula(obj_not_eq_implies_quantify,
	 * obj2_eq_impl_quantify, Connector.AND ); return f; }
	 */
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
				.getQuantifiedExpression();
		//ref
		Expression objDeref = getObjectDereferenced();
		Expression _class = getType();
		///////////
		/*
		 * Variable obj1 = new Variable(FreshIntGenerator.getInt(),
		 * JavaReferenceType.ReferenceType);
		 */
		Variable obj1 = new Variable(FreshIntGenerator.getInt());
		Predicate2Ar obj_not_eq_arr_Ref = new Predicate2Ar(obj1, objDeref,
				PredicateSymbol.NOTEQ);
		// (ref.a[i]).generalise(ref, obj) = obj.a[i]
		Expression objArr = quantifiedExpression.copy();
		objArr = objArr.generalize(objDeref, obj1);
		//variable that represents the index of the array
		Variable varIndex = (Variable) arrayModified.getQuantificator()[0]
				.getBoundVar();
		Quantificator quantificators = new Quantificator(Quantificator.FORALL,
				varIndex, Formula.getFormula(new Predicate2Ar(varIndex,
						new NumberLiteral(0), PredicateSymbol.GRTEQ),
						new Predicate2Ar(varIndex, new FieldAccess(
								ArrayLengthConstant.ARRAYLENGTHCONSTANT, objArr
										.getSubExpressions()[0].copy()),
								PredicateSymbol.LESS), Connector.AND));
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
		Formula quantify_obj_arr_i1_i2 = new QuantifiedFormula(obj_arr_i1_i2,
				quantificators);
		Formula obj_not_eq_implies = Formula.getFormula(obj_not_eq_arr_Ref,
				quantify_obj_arr_i1_i2, Connector.IMPLIES);
		Formula domain1 = new Predicate2Ar(obj1.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Quantificator q1 = new Quantificator(Quantificator.FORALL, obj1,
				domain1);
		/*
		 * forall o:Type (Type <: type(this) ) o != ref ==> forall i :int.( 0 = <
		 * i < o.a.length ). o.a[i] == old(o.a[i])
		 */
		Formula obj_not_eq_implies_quantify = Formula.getFormula(
				obj_not_eq_implies, q1);
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
		Variable obj2 = new Variable(FreshIntGenerator.getInt());
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
		Quantificator[] quantificators2 = new Quantificator[arrayModified
				.getQuantificator().length];
		System.arraycopy(arrayModified.getQuantificator(), 0, quantificators2,
				0, quantificators2.length);
		Expression _v = quantificators2[0].getBoundVar();
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
		quantificators2[0] = new Quantificator(Quantificator.FORALL, i, domain2);
		Formula obj2_eq_impl = Formula.getFormula(
				this_arr_out_of_interval_unchanged, quantificators2);
		Formula domain3 = new Predicate2Ar(obj2.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Quantificator q3 = new Quantificator(Quantificator.FORALL, obj2,
				domain3);
		Formula obj2_eq_impl_quantify = new QuantifiedFormula(Formula
				.getFormula(obj2_eq_arr_Ref, obj2_eq_impl, Connector.IMPLIES),
				q3);
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
				.getQuantifiedExpression();
		Quantificator[] quantificators = arrayModified.getQuantificator();
		//ref
		Expression objDeref = getObjectDereferenced();
		Expression _class = getType();
		///////////
		Variable obj1 = new Variable(FreshIntGenerator.getInt(), new Variable(
				FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
		Predicate2Ar obj_not_eq_arr_Ref = new Predicate2Ar(obj1, objDeref,
				PredicateSymbol.NOTEQ);
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
		Quantificator q1 = new Quantificator(Quantificator.FORALL, obj1,
				domain1);
		/*
		 * forall o:Type (Type <: type(this) ) o != ref ==> forall i :int.( i1= <
		 * i <i2). o.a[i] == old(o.a[i])
		 *  
		 */
		Formula obj_not_eq_implies_quantify = Formula.getFormula(
				obj_not_eq_implies, q1);
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
		Quantificator q = new Quantificator(Quantificator.FORALL, i, domain);
		QuantifiedExpression f = new QuantifiedExpression(q,
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
