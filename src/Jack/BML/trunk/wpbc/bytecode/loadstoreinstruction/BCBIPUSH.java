/*
 * Created on Apr 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.loadstoreinstruction;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import formula.Formula;

import bcexpression.Expression;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;

/**
 * @author mpavlova
 *
 *  Operation : Push byte
 *
 *  Format: <code> bipush</code> 	byte 	 
 * 
 *  Operand Stack : ... ==> ..., value
 *	
 *  Description: The immediate byte is sign-extended to an int value. That value is pushed onto the operand stack. 
 * 
 * wp = psi^n[t <-- t+1] [S(t+1) <-- value]
 */
public class BCBIPUSH extends BCConstantPUSHInstruction {
	/**
	 * @param _instruction
	 */
	public BCBIPUSH(InstructionHandle _instruction) {
		super(_instruction);
		setType(JavaType.JavaBYTE);
	}



}
