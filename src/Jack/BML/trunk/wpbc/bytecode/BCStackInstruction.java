/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import formula.Formula;

/**
 * @author mpavlova
 *
 *  class for all stack operations     DUP, DUP_X1, DUP_X2, DUP2, DUP2_X1, DUP2_X2, POP, POP2, SWAP
 */
public class BCStackInstruction extends BCInstruction {
	//    DUP, DUP_X1, DUP_X2, DUP2, DUP2_X1, DUP2_X2, POP, POP2, SWAP
	
	/**
	 * @param _instruction
	 */
	public BCStackInstruction(InstructionHandle _instruction) {
		super(_instruction);
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}

}
