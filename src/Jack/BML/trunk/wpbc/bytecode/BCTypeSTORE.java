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
import org.apache.bcel.generic.LocalVariableInstruction;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeSTORE extends BCInstruction  implements BCLocalVariableInstruction{
	//ASTORE, DSTORE, FSTORE, ISTORE, LSTORE
	/**
	 * index of local variable 
	 */
	private int index ;
	
	/**
	 * @param _instruction
	 */
	public BCTypeSTORE(InstructionHandle _instruction) {
		super(_instruction);
		setIndex(((LocalVariableInstruction)(_instruction.getInstruction())).getIndex());
		
		// TODO Auto-generated constructor stub
	}

	/**
	 * @see bytecode.BCLocalVariableInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		index = _index;
	}
	/**
	 * @see bytecode.BCLocalVariableInstruction#getIndex()
	 */
	public int getIndex() {
		return index;
	}
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}

}
