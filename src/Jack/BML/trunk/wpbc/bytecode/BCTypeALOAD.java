/*
 * Created on Mar 31, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import constants.ArrayLengthConstant;

import specification.ExceptionalPostcondition;

import bcexpression.ArithmeticExpression;
import bcexpression.ExpressionConstants;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Counter;
import bcexpression.vm.Stack;
import bcexpression.ArrayAccessExpression;
import bcexpression.Expression;
import bcexpression.FieldAccessExpression;

import formula.Formula;
import formula.Connector;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeALOAD  extends BCExceptionThrower implements  BCTypedInstruction {
	//    ..., arrayref, index  ==> ..., value

	//AALOAD, BALOAD, LALOAD, CALOAD, IALOAD, DALOAD , FALOAD, SALOAD
	private JavaType type;
	/**
	 * @param _instruction
	 */
	public BCTypeALOAD(InstructionHandle _instruction, JavaType _type ) {
		super(_instruction);
		setType(_type );
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType()  {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType()
	 */
	public void setType(JavaType _type) {
		type = _type;
	}
	
	public Formula wp(Formula _n_Postcondition, ExceptionalPostcondition _e_Postcondition) {
		 Formula wp = null ; 
		  //normal execution 
		  Stack _stackTop = new Stack(Expression.getCounter());
		  Stack _stackTop_minus_1 =  new Stack(Expression.getCounter_minus_1());
		 
		  //t <------ t -1
		  _n_Postcondition.substitute(Expression.getCounter(), Expression.getCounter_minus_1());
		// n_post[ S(t) <----- S(t-1)[S(t)]]
		_n_Postcondition = _n_Postcondition.substitute( _stackTop,  new ArrayAccessExpression( _stackTop_minus_1, _stackTop));			
			
		  //S(t - 1) != null
		  Formula _arr_not_null = new Predicate2Ar(_stackTop_minus_1, Expression.NULL,  PredicateSymbol.NOTEQ );
	  
	  
		  //S(t-1).length > S( t )
		  FieldAccessExpression _arrlength = new FieldAccessExpression( new ArrayLengthConstant(), _stackTop_minus_1 ) ;
		  Formula  _arr_index_correct = new Predicate2Ar( _arrlength,   _stackTop,  PredicateSymbol.GRT);
		  Formula _condition = new Formula(_arr_not_null, _arr_index_correct,  Connector.AND);
		  Formula _normal_termination = new Formula(_condition, _n_Postcondition , Connector.IMPLIES );
	  
		
		  //  execution terminating with java.lang.IndexOutOfBoundsException
		  //S(t-1).length <= S(t) ==> excPost(IndexOutOfBoundsException)
		  Formula _index_out_of_bounds = new Predicate2Ar( _arrlength,   _stackTop,  PredicateSymbol.LESSEQ); 
		  Formula _wp_arr_out_of_bounds = getWpForException(JavaType.getJavaClass("java.lang.IndexOutOfBoundsException"), _e_Postcondition);
		  Formula _out_of_bound_termination = new Formula(_index_out_of_bounds, 
																							_wp_arr_out_of_bounds , 
																							Connector.IMPLIES);

		  // execution terminating with  NullPointerException
		  //S(t-1) == null ==> excPost(NullPointerException) 
		  Formula _arr_null = new Predicate2Ar(_stackTop_minus_1, Expression.NULL,  PredicateSymbol.EQ );
		  Formula _wp_null_pointer =  getWpForException(JavaType.getJavaClass("java.lang.NullPointerException"), _e_Postcondition);;
		  Formula _null_pointer_termination = new Formula(_arr_null, 
														  _wp_null_pointer,
														  Connector.IMPLIES);
		  Formula[] _formulas = new Formula[3];
		  _formulas[0] = _normal_termination;
		  _formulas[1] = _null_pointer_termination;
		  _formulas[2] = _out_of_bound_termination;
		  wp = new Formula( _formulas, Connector.AND); 
		  //wp.substitute(_counter, new ArithmeticExpression( _counter, new NumberLiteral(new Integer(1)) , ExpressionConstants.MINUS)) ;
		  return wp;
		 }

}
