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
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * iastore
 *
 * Operation : Store into int array
 *
 * Format :  iastore 	
 * 
 * Operand Stack : ..., arrayref, index, value  ==> ...
 *
 * Description : The arrayref must be of type reference and must refer to an array whose 
 * components are of type int. Both index and value must be of type int. The arrayref, index, and 
 * value are popped from the operand stack. The int value is stored as the component of the array indexed by index. 
 *
 * Runtime Exceptions :
 * If arrayref is null, iastore throws a NullPointerException. 
 * Otherwise, if index is not within the bounds of the array referenced by arrayref, 
 * the iastore instruction throws an ArrayIndexOutOfBoundsException
 */
public class BCTypeASTORE
	extends BCExceptionThrower
	implements BCTypedInstruction {
	private JavaType type;
	//    .., arrayref, index, value  ==> ...  
	//assigns to arrayref[index] value

	/**
	 * @param _instruction
	 */
	public BCTypeASTORE(InstructionHandle _instruction, JavaType _type) {
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
	 * @see bytecode.BCTypedInstruction#setType(org.apache.bcel.generic.TypedInstruction, org.apache.bcel.generic.ConstantPoolGen)
	 */
	public void setType(JavaType _type) {
		type = _type;
	}
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, java.util.HashMap)
	 */
	public Formula wp(
		IJml2bConfiguration config,
		Formula _n_Postcondition, ExsuresTable _exc_Postcondition) {

		return null;
	}
	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Stack stackTop = new Stack(Expression.COUNTER);

		//t <------ t - 3
		vcs.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_3());

		//S(t-2 ) != null
		Formula array_not_null =
			Formula.getFormula( 
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_2()),
				Expression._NULL,
				PredicateSymbol.EQ), Connector.NOT );
		//S(t-1) < S(t-2).length
		Formula index_le_arr_len =
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_1()),
				new FieldAccess(
						ArrayLengthConstant.ARRAYLENGTHCONSTANT,
			new Stack(Expression.getCOUNTER_MINUS_2())),
				PredicateSymbol.LESS);

		
		//S(t-1) >= 0
		Formula index_greq_0=
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_1()),
				new NumberLiteral(0),
				PredicateSymbol.GRTEQ);

		
		Expression arrElementAtIndex =
			new ArrayAccessExpression(new Stack(Expression.getCOUNTER_MINUS_2()), new Stack(Expression.getCOUNTER_MINUS_1()));
		//S(t-2)[S(t-1)] <--- S(t)

		vcs.substitute(arrElementAtIndex, stackTop);
		
		
		Integer key1 = vcs.addHyp(getPosition(), array_not_null);
		vcs.addHypsToVCs(key1);
			
		Integer key2 = vcs.addHyp(getPosition(), index_le_arr_len);
		vcs.addHypsToVCs(key2);
		
		Integer key3 = vcs.addHyp(getPosition(), index_greq_0);
		vcs.addHypsToVCs(key3);
		
		//exceptional termination
		//S(t-2 ) == null ==> _exc_Postcondition(java.lang.NullPointerException)
		Formula array_null =
			new Predicate2Ar(
			new Stack(Expression.getCOUNTER_MINUS_2()),
				Expression._NULL,
				PredicateSymbol.EQ);
		VCGPath nullPointer =
			getWpForException(config,
				(JavaObjectType) JavaType.getJavaRefType(
					ClassNames.NULLPOINTERException));
		Integer key4 = nullPointer.addHyp(getPosition(), array_null);
		nullPointer.addHypsToVCs(key4);
		nullPointer.setInstrIndex(getPosition());
		
		
		//S(t-1) > S(t-2).length || S(t-1) < 0 ==> _exc_Postcondition(java.lang. ArrayIndexOutOfBoundsException)
		
		Formula indGrtLen = new Predicate2Ar(
				new Stack(Expression.getCOUNTER_MINUS_1()),
				new FieldAccess(
						ArrayLengthConstant.ARRAYLENGTHCONSTANT,
			new Stack(Expression.getCOUNTER_MINUS_2())),
				PredicateSymbol.GRTEQ);
		Formula indLe0 = new Predicate2Ar(
				new Stack(Expression.getCOUNTER_MINUS_1()),
				new NumberLiteral(0 ),
				PredicateSymbol.LESS);
		
		Formula arr_index_not_correct = Formula.getFormula( indGrtLen, indLe0, Connector.OR);
		
		VCGPath outOfBounds =
			getWpForException(config,
				(JavaObjectType) JavaType.getJavaRefType(
					ClassNames.ARRAYINDEXOUTOFBOUNDException));
		/*Util.dump(" excPost" + outOfBounds);*/
		Integer key5 = outOfBounds.addHyp(getPosition(),  arr_index_not_correct);
		outOfBounds.addHypsToVCs(key5);
		
		outOfBounds.setInstrIndex(getPosition() );
		
		vcs.merge(nullPointer);
		vcs.merge(outOfBounds);
		return vcs;
	}
}
