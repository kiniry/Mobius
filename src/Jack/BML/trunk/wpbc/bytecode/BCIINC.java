package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;

import formula.Formula;

import org.apache.bcel.generic.LocalVariableInstruction;
/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCIINC extends BCInstruction implements BCLocalVariableInstruction{
	
	private int index;
	
	public BCIINC(InstructionHandle _instruction) {
		super(_instruction);
		setIndex(((LocalVariableInstruction)(_instruction.getInstruction())).getIndex());
		
		// TODO Auto-generated constructor stub
	}
	
	
	/**
	 * @see bytecode.BCInstruction#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula arg0, ExceptionalPostcondition arg1) {
		return null;
	}
	/**
	 * @see bytecode.BCLocalVariableInstruction#BCLocalVariableInstruction()
	 */
	public void BCLocalVariableInstruction() {
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

}
