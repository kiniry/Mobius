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
import bcexpression.ArrayAccessExpression;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.LocalVariable;
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
	 * method returns the object for which the array is accessed, i.e. for ( [,
	 * arr(local(0)) , 2)
	 * 
	 * @return
	 */

	/**
	 * @return forall o : ElemType( ). forall i:int . (i >= startInterval && i = <
	 *         endInterval) . o != array[i]
	 */
	public Expression getPostCondition() {
		SpecArray specArr = getSpecArray();
		Formula condition = null;
		if (specArr instanceof ArrayElemFromTo) {
			
			condition = (Formula)getConditionForInterval();
			 
			return condition;
		}
		if (specArr instanceof AllArrayElem) {
			
			  condition = (Formula)getConditionForAll();
			 
			return condition;
		}
		if (specArr instanceof SingleIndex) {
			condition = (Formula) getConditionForSingleIndice();
			return condition;
		}
		return null;
	}
	/**
	 * forall o: Type (Type <: _class) o != arrRef ==> old( arr(o)) == arr( o)
	 * and forall o: Type (Type <: _class). forall j :int( j!=i ) o == arrRef
	 * ==> old( f^s(o)) == f^s( o) s is the all the other fields of arr.
	 * 
	 * @return
	 */
	public Expression getConditionForSingleIndice() {
		//		forall o: Type (Type <: _class) o != arrRef ==> old( arr(o)) == arr(
		// o)
		Expression arrayModified = getExpression();
		Expression objDeref = getObjectDereferenced();
		Expression index = ((SingleIndex) getSpecArray()).getIndex();
		//////////////////////////////////////////////////
		Expression _class = ModifiesExpression.getClass(objDeref,
				getConstantPool());
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
		///////////////////////////////////////////////////////////////
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
		Variable obj2 = new Variable(FreshIntGenerator.getInt(), new Variable(
				FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
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
		Predicate2Ar f2 = new Predicate2Ar(thisArray, new OLD(thisArray),
				PredicateSymbol.EQ);
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
public Expression getConditionForInterval() {
		Expression ind1 = ((ArrayElemFromTo)getSpecArray()).getStart();
		Expression ind2 = ((ArrayElemFromTo)getSpecArray()).getEnd();
		// forall i :int( i1=< i <i2). ref.a[i]
		QuantifiedExpression arrayModified = (QuantifiedExpression) getExpression();
		//ref.a[i]
		Expression quantifiedExpression = arrayModified
				.getQuantifiedExpression();
		Quantificator[] quantificators = arrayModified.getQuantificator();
		//ref
		Expression objDeref = getObjectDereferenced();
		Expression _class = ModifiesExpression.getClass(objDeref,
				getConstantPool());
		
		///////////
		Variable obj1 = new Variable(FreshIntGenerator.getInt(), new Variable(
				FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
		Predicate2Ar obj_not_eq_arr_Ref = new Predicate2Ar(obj1, objDeref,
				PredicateSymbol.NOTEQ);
		 // (ref.a[i]).generalise(ref, obj) = obj.a[i]
		Expression objArr = quantifiedExpression.copy();		
		objArr = objArr.generalize(objDeref, obj1);
		
		// obj.a[ i ] == old(obj.a[ i ] )
		Predicate2Ar obj_arr_i1_i2 = new Predicate2Ar(objArr, new OLD(objArr), PredicateSymbol.EQ );
		Formula quantify_obj_arr_i1_i2 = new QuantifiedFormula( obj_arr_i1_i2 , quantificators);
		
		Formula obj_not_eq_implies = Formula.getFormula( obj_not_eq_arr_Ref, quantify_obj_arr_i1_i2, Connector.IMPLIES);
		
		Formula domain1 = new Predicate2Ar(obj1.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Quantificator q1 = new Quantificator(Quantificator.FORALL, obj1, domain1);
		
		/*
		 * forall o:Type (Type <: type(this) ) o != ref ==> forall i :int.( i1= <
		 * i <i2). o.a[i] == old(o.a[i])
		 *  
		 */ 
		Formula obj_not_eq_implies_quantify = Formula.getFormula(obj_not_eq_implies, q1 );
		
		
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////
		Variable obj2 = new Variable(FreshIntGenerator.getInt(), new Variable(
				FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
		Predicate2Ar obj2_eq_arr_Ref = new Predicate2Ar(obj2, objDeref,
				PredicateSymbol.EQ);

		Variable i = new Variable(FreshIntGenerator.getInt(), JavaType.JavaINT);
		 
		Predicate2Ar i_less_ind1 = new Predicate2Ar(i, ind1, PredicateSymbol.LESS );
		Predicate2Ar i_grte_0 = new Predicate2Ar(i, new NumberLiteral(0), PredicateSymbol.GRTEQ);
		Predicate2Ar i_grt_ind2 = new Predicate2Ar(i, ind2, PredicateSymbol.GRT);
		Expression arrLength = new FieldAccess( new ArrayLengthConstant(), getModifies().getExpression());
		Predicate2Ar i_leq_arr_length = new Predicate2Ar(i, arrLength, PredicateSymbol.LESS);
		
		Formula domain2 = Formula.getFormula(i_leq_arr_length, 
										Formula.getFormula(i_grt_ind2,  
												Formula.getFormula( i_less_ind1, 
														i_grte_0, Connector.AND ) , 
														Connector.AND) , Connector.AND);
		
		
		Quantificator[] quantificators2 = new Quantificator[quantificators.length];
		System.arraycopy(quantificators , 0, quantificators2, 0, quantificators.length); 
		Expression _v = quantificators2[0].getBoundVar();
		Expression array = quantifiedExpression.copy().substitute(objDeref, obj2);
		array = array.substitute(_v, i);
		
		Predicate2Ar this_arr_out_of_interval_unchanged = new Predicate2Ar( array, new OLD(array), PredicateSymbol.EQ);
		quantificators2[0]  = new Quantificator(Quantificator.FORALL, i, domain2 );
		
		Formula obj2_eq_impl = Formula.getFormula(this_arr_out_of_interval_unchanged, quantificators2);
		Formula domain3 = new Predicate2Ar(obj2.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Quantificator q3 = new Quantificator(Quantificator.FORALL, obj2, domain3);
		Formula obj2_eq_impl_quantify = new QuantifiedFormula(Formula.getFormula(obj2_eq_arr_Ref, obj2_eq_impl, Connector.IMPLIES ), q3  );
		
		Formula f = Formula.getFormula(obj_not_eq_implies_quantify, obj2_eq_impl_quantify, Connector.AND );
		
		return f;
	}	/**
		  * for all (index : 0 <= index < length(array)) o != array[index]
		  * 
		  * @param o
		  * @return
		  */
	public Expression getConditionForAll() {
		Expression array = getModifies().getExpression();
		Expression ind1 = new NumberLiteral( 0);
		Expression ind2 = new FieldAccess(new ArrayLengthConstant(), array );
		// forall i :int( i1=< i <i2). ref.a[i]
		QuantifiedExpression arrayModified = (QuantifiedExpression) getExpression();
		//ref.a[i]
		Expression quantifiedExpression = arrayModified
				.getQuantifiedExpression();
		Quantificator[] quantificators = arrayModified.getQuantificator();
		//ref
		Expression objDeref = getObjectDereferenced();
		Expression _class = ModifiesExpression.getClass(objDeref,
				getConstantPool());
		
		///////////
		Variable obj1 = new Variable(FreshIntGenerator.getInt(), new Variable(
				FreshIntGenerator.getInt(), JML_CONST_TYPE.JML_CONST_TYPE));
		Predicate2Ar obj_not_eq_arr_Ref = new Predicate2Ar(obj1, objDeref,
				PredicateSymbol.NOTEQ);
		 // (ref.a[i]).generalise(ref, obj) = obj.a[i]
		Expression objArr = quantifiedExpression.copy();		
		objArr = objArr.generalize(objDeref, obj1);
		
		// obj.a[ i ] == old(obj.a[ i ] )
		Predicate2Ar obj_arr_i1_i2 = new Predicate2Ar(objArr, new OLD(objArr), PredicateSymbol.EQ );
		Formula quantify_obj_arr_i1_i2 = new QuantifiedFormula( obj_arr_i1_i2 , quantificators);
		
		Formula obj_not_eq_implies = Formula.getFormula( obj_not_eq_arr_Ref, quantify_obj_arr_i1_i2, Connector.IMPLIES);
		
		Formula domain1 = new Predicate2Ar(obj1.getType(), _class,
				PredicateSymbol.SUBTYPE);
		Quantificator q1 = new Quantificator(Quantificator.FORALL, obj1, domain1);
		
		/*
		 * forall o:Type (Type <: type(this) ) o != ref ==> forall i :int.( i1= <
		 * i <i2). o.a[i] == old(o.a[i])
		 *  
		 */ 
		Formula obj_not_eq_implies_quantify = Formula.getFormula(obj_not_eq_implies, q1 );
		
		
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
			end = new FieldAccess(new ArrayLengthConstant(), modExpr);
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
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		// TODO Auto-generated method stub
		return null;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = getModifies().toString() + " [" + getSpecArray() +  "]";
		return s;
	}
}
