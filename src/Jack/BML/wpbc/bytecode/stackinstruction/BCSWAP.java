/*
 * Created on Apr 21, 2004
 *
 * 
 */
package bytecode.stackinstruction;

import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.Variable;
import bcexpression.vm.Stack;
import bytecode.BCInstruction;

/**
 * @author mpavlova
 *
 * swap
 *
 * Operation :    Swap the top two operand stack values
 *
 * Operand Stack
 *
 *  ..., value2, value1 ==> ..., value1, value2
 *
 * Description:  Swap the top two values on the operand stack. The swap instruction must not be used unless value1 and value2 are both values of a category 1 computational type (?3.11.1).
 *
 * wp = psi^n[ s(t) <-- x][ s(t -1) <-- s(t) ][ x <-- S(t-1)  ]
 * */ 
public class BCSWAP  extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCSWAP(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp = null;
		
		
		
		wp = (Formula)_normal_Postcondition.substitute(new Stack(Expression.COUNTER ) , Variable.DummyVariable );
		wp = (Formula)wp.substitute(new Stack(Expression.getCOUNTER_MINUS_1() ), new Stack( Expression.COUNTER));
		wp = (Formula)wp.substitute( Variable.DummyVariable , new Stack( Expression.getCOUNTER_MINUS_1()));
		return wp; 
	} 

}
