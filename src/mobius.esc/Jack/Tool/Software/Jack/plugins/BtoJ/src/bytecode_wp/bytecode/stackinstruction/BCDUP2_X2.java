/*
 * Created on Apr 21, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.stackinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * dup2_x2
 * 
 * Operation : Duplicate the top one or two operand stack values and insert two, three, or four values down
 * 
 * Operand Stack

    Form 1:

    ..., value4, value3, value2, value1 ==>  ..., value2, value1, value4, value3, value2, value1

    where value1, value2, value3, and value4 are all values of a category 1 computational type (?3.11.1).

    Form 2:

    ..., value3, value2, value1 ==> ..., value1, value3, value2, value1

    where value1 is a value of a category 2 computational type and value2 and value3 are both values of a category 1 computational type (?3.11.1).

    Form 3:

    ..., value3, value2, value1 ==> ..., value2, value1, value3, value2, value1

    where value1 and value2 are both values of a category 1 computational type and value3 is a value of a category 2 computational type (?3.11.1).

    Form 4:

    ..., value2, value1 == >..., value1, value2, value1

    where value1 and value2 are both values of a category 2 computational type
    
    NB : here only Form 1 is considered
 */
public class BCDUP2_X2 extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCDUP2_X2(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		
//		Stack topStack_plus2 = new Stack(Expression.COUNTER_PLUS_2);
//		Stack topStack_plus1 = new Stack(Expression.COUNTER_PLUS_1);
		Stack topStack = new Stack(Expression.COUNTER);
		Stack topStack_minus1 = new Stack(Expression.getCOUNTER_MINUS_1());
		Stack topStack_minus2 = new Stack(Expression.getCOUNTER_MINUS_2());
		
		wp =(Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_2() );
		wp = (Formula)wp.substitute(new Stack(Expression.getCOUNTER_PLUS_2()) , topStack );
		wp = (Formula)wp.substitute(new Stack(Expression.getCOUNTER_PLUS_1()) , topStack_minus1 );
		
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Stack topStack = new Stack(Expression.COUNTER);
		Stack topStack_minus1 = new Stack(Expression.getCOUNTER_MINUS_1());
		Stack topStack_minus2 = new Stack(Expression.getCOUNTER_MINUS_2());
		
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_2() );
		vcs.substitute(new Stack(Expression.getCOUNTER_PLUS_2()) , topStack );
		vcs.substitute(new Stack(Expression.getCOUNTER_PLUS_1()) , topStack_minus1 );
		
		return vcs;
	}

}
