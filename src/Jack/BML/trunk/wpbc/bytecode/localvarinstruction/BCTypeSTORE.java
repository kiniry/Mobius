/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.localvarinstruction;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import formula.Formula;

import bcclass.BCLocalVariable;
import bcexpression.Expression;
import bcexpression.LocalVariableAccess;
import bcexpression.vm.Stack;


/**
 * @author mpavlova
 *
 * Operation: Store the stack top  into local variable
 * 
 * Format : astore index 	
 * 
 * Operand Stack:   ..., objectref ==> ...
 * 
 * wp = psi^n[t < -- t -1][o ==local(index)  <-- S( t)] 
 */
public class BCTypeSTORE extends BCLocalVariableInstruction {
	//ASTORE, ISTORE, LSTORE
	
	/**
	 * @param _instruction
	 */
	public BCTypeSTORE(InstructionHandle _instruction, BCLocalVariable _lv) {
		super(_instruction, _lv);
		setType(_lv.getType());
	}

	/* (non-Javadoc)
		 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
		 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExceptionalPostcondition _exc_Postcondition) {
		Formula wp;
		wp = _normal_Postcondition.substitute(Expression.getCounter(), Expression.getCounter_minus_1());
		Stack stackTop = new Stack(Expression.getCounter());
		wp = wp.substitute(new LocalVariableAccess(getIndex()), stackTop  );
		return wp;
	}
}
