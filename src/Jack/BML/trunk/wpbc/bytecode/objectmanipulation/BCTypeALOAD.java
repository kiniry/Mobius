/*
 * Created on Mar 31, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.InstructionHandle;

import constants.ArrayLengthConstant;

import bcclass.attributes.ExsuresTable;
import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;

import bcexpression.vm.Stack;
import bcexpression.ArrayAccessExpression;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.NumberLiteral;
import bytecode.BCExceptionThrower;
import bytecode.BCTypedInstruction;

import formula.Formula;
import formula.Connector;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 * aload
 *
 * Operation : Load int from array
 *
 *  Format : iaload 	
 *
 * 
 * Operand Stack :  ..., arrayref, index  == > ..., value
 *
 * Description : The arrayref must be of type reference and must refer to an array whose components are of type int. The index must be of type int. Both arrayref and index are popped from the operand stack. The int value in the component of the array at index is retrieved and pushed onto the operand stack.
 *
 * Runtime Exceptions :  If arrayref is null, iaload throws a NullPointerException. Otherwise, if index is not 
 * within the bounds of the array referenced by arrayref, the iaload instruction throws an ArrayIndexOutOfBoundsException.
 */
public class BCTypeALOAD
	extends BCExceptionThrower
	implements BCTypedInstruction {
	//    ..., arrayref, index  ==> ..., value

	//AALOAD, BALOAD, LALOAD, CALOAD, IALOAD, DALOAD , FALOAD, SALOAD
	private JavaType type;
	/**
	 * @param _instruction
	 */
	public BCTypeALOAD(InstructionHandle _instruction, JavaType _type) {
		super(_instruction);
		setType(_type);
		setExceptionsThrown(
			new JavaObjectType[] {
				(JavaObjectType) JavaObjectType.getJavaRefType(
					ClassNames.NULLPOINTERException),
				(JavaObjectType) JavaObjectType.getJavaRefType(
					ClassNames.ARRAYINDEXOUTOFBOUNDException)});
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType()
	 */
	public void setType(JavaType _type) {
		type = _type;
	}

	public Formula wp(
		Formula _n_Postcondition,
		ExsuresTable _e_Postcondition) {
		Formula wp = null;
		//normal execution 
		//Stack _stackTop = new Stack(Expression.COUNTER);
		//Stack _stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);

		//t <------ t -1
		_n_Postcondition.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		// n_post[ S(t) <----- S(t-1)[S(t)]]
		_n_Postcondition =
		(Formula)_n_Postcondition.substitute(
			new Stack(Expression.getCOUNTER_MINUS_1()),
				new ArrayAccessExpression(new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER)));

		//S(t - 1) != null
		Formula _arr_not_null =
			Formula.getFormula( 
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_1()),
				Expression._NULL,
				PredicateSymbol.EQ), Connector.NOT);

		//S(t-1).length > S( t )
		FieldAccess _arrlength =
			new FieldAccess(
					ArrayLengthConstant.ARRAYLENGTHCONSTANT,
			new Stack(Expression.getCOUNTER_MINUS_1()));
		Formula _index_less_len =
			new Predicate2Ar(_arrlength, new Stack(Expression.COUNTER), PredicateSymbol.GRT);
		Formula _index_grt_eq_0 = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0) , PredicateSymbol.GRTEQ);
		
		Formula _arr_index_correct = Formula.getFormula(_index_less_len, _index_grt_eq_0, Connector.AND );
		Formula _condition =
		Formula.getFormula(_arr_not_null, _arr_index_correct, Connector.AND);
		Formula _normal_termination =
		Formula.getFormula(_condition, _n_Postcondition, Connector.IMPLIES);

		//  execution terminating with java.lang.IndexOutOfBoundsException
		//S(t-1).length <= S(t) || ==> excPost(IndexOutOfBoundsException)
		Formula _index_grt_eq_len =
			new Predicate2Ar(_arrlength.copy(), new Stack(Expression.COUNTER), PredicateSymbol.LESSEQ);
		Formula _index_less_0 = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.LESS);
		Formula _index_out_of_bounds  = Formula.getFormula( _index_grt_eq_len, _index_less_0, Connector.OR);
		
		Formula _wp_arr_out_of_bounds =
			getWpForException(
				(JavaObjectType) JavaType.getJavaRefType(
					"Ljava/lang/IndexOutOfBoundsException;"));
		Formula _out_of_bound_termination =
		Formula.getFormula(
				_index_out_of_bounds,
				_wp_arr_out_of_bounds,
				Connector.IMPLIES);

		// execution terminating with  NullPointerException
		//S(t-1) == null ==> excPost(NullPointerException) 
		Formula _arr_null =
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_1()),
				Expression._NULL,
				PredicateSymbol.EQ);
		Formula _wp_null_pointer =
			getWpForException(
				(JavaObjectType) JavaType.getJavaRefType(
					"java.lang.NullPointerException"));
		;
		Formula _null_pointer_termination =
		Formula.getFormula(_arr_null, _wp_null_pointer, Connector.IMPLIES);
		Formula[] _formulas = new Formula[3];
		_formulas[0] = _normal_termination;
		_formulas[1] = _null_pointer_termination;
		_formulas[2] = _out_of_bound_termination;
		wp = Formula.getFormula(_formulas, Connector.AND);
		//wp.substitute(_counter, new ArithmeticExpression( _counter, new NumberLiteral(new Integer(1)) , ExpressionConstants.MINUS)) ;
		return wp;
		//return _normal_termination;
	}

}
