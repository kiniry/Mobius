/*
 * Created on Mar 31, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.objectmanipulation;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.ArrayAccessExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.ClassNames;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCExceptionThrower;
import bytecode_wp.bytecode.BCTypedInstruction;
import bytecode_wp.constants.ArrayLengthConstant;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.VCGPath;

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
		IJml2bConfiguration config,
		Formula _n_Postcondition, ExsuresTable _e_Postcondition) {
		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
	
//		normal execution 
		//Stack _stackTop = new Stack(Expression.COUNTER);
		//Stack _stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);

		//t <------ t -1
		vcs.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		// n_post[ S(t) <----- S(t-1)[S(t)]]
		vcs.substitute(
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
		Integer key1 = vcs.addHyp(getPosition(),_arr_not_null );
		vcs.addHypsToVCs( key1);
		Integer key2 = vcs.addHyp(getPosition(),_arr_index_correct );
		vcs.addHypsToVCs( key2);

		//  execution terminating with java.lang.IndexOutOfBoundsException
		//S(t-1).length <= S(t) || ==> excPost(IndexOutOfBoundsException)
		Formula _index_grt_eq_len =
			new Predicate2Ar( new Stack(Expression.COUNTER),_arrlength.copy(), PredicateSymbol.GRTEQ);
		Formula _index_less_0 = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.LESS);
		Formula _index_out_of_bounds  = Formula.getFormula( _index_grt_eq_len, _index_less_0, Connector.OR);
		
		VCGPath _wp_arr_out_of_bounds =
			getWpForException(config,
				(JavaObjectType) JavaType.getJavaRefType(
					"Ljava/lang/ArrayIndexOutOfBoundsException;") );
		
		_wp_arr_out_of_bounds.setInstrIndex( getPosition());
		Integer key3 = _wp_arr_out_of_bounds.addHyp(getPosition(),_index_out_of_bounds );
		_wp_arr_out_of_bounds.addHypsToVCs( key3); 
		
		

		// execution terminating with  NullPointerException
		//S(t-1) == null ==> excPost(NullPointerException) 
		Formula _arr_null =
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_1()),
				Expression._NULL,
				PredicateSymbol.EQ);
		VCGPath _wp_null_pointer =
			getWpForException(config,
				(JavaObjectType) JavaType.getJavaRefType(
					"java.lang.NullPointerException"));
		_wp_null_pointer.setInstrIndex( getPosition());
		Integer key4 = _wp_null_pointer.addHyp(getPosition(),_arr_null );
		_wp_null_pointer.addHypsToVCs( key4); 
		
		vcs.merge(_wp_arr_out_of_bounds );
		vcs.merge( _wp_null_pointer);
		return vcs;
	}

}
