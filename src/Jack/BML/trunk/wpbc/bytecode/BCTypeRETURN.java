package bytecode;

import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;

import bcexpression.vm.Stack;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeRETURN  extends BCInstruction implements EndBlock {
	
	/**
	 * @param _instruction
	 */
	public BCTypeRETURN(InstructionHandle _instruction) {
		super(_instruction);
	}
	
	public Formula wp(Formula  _nPostcondition, ExceptionalPostcondition _ePostcondition) {
		return null;
	}
	
	
}
