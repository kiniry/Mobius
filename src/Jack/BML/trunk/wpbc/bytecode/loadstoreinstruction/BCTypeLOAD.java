/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.loadstoreinstruction;


import org.apache.bcel.generic.InstructionHandle;

import bcclass.BCLocalVariable;
import bcexpression.Expression;
import bcexpression.LocalVariableAccess;
import bcexpression.vm.Stack;

import specification.ExceptionalPostcondition;
import formula.Formula;

/**
 * @author mpavlova
 *
 * Operation: Load reference from local variable
 * 
 * Operand Stack : ... ==> ..., objectref
 * 
 * Description:   The index is an unsigned byte that must be an index into the local variable array of the current frame. 
 * The local variable at index must contain a reference. 
 * The objectref in the local variable at index is pushed onto the operand stack.
 * 
 *  wp = psi^n[t <-- t +1][S(t+1) <-- local(i)]
 */
public  class BCTypeLOAD  extends  BCLocalVariableInstruction{
	//ALOAD,  ILOAD, LLOAD 

	/**
	 * @param _instruction
	 */
	public BCTypeLOAD(InstructionHandle _instruction, BCLocalVariable _lv) {
		super(_instruction, _lv);
		setType(_lv.getType());
		// TODO Auto-generated constructor stub
	}

	

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		Formula wp;
		wp = _normal_Postcondition.substitute(Expression.getCounter(), Expression.getCounter_plus_1());
		Stack topStack= new Stack( Expression.getCounter_plus_1());
		wp = wp.substitute(topStack, new LocalVariableAccess(getIndex()));
		return wp;
	}

}
