package bytecode.localvarinstruction;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;

import formula.Formula;

import org.apache.bcel.generic.LocalVariableInstruction;

import bcexpression.javatype.JavaType;
import bytecode.BCInstruction;

/**
 * @author mpavlova
 *
 */
public class BCIINC extends BCInstruction implements BCLocalVariableInstruction{
	
	private int index;
	
	public BCIINC(InstructionHandle _instruction) {
		super(_instruction);
		setIndex(((LocalVariableInstruction)(_instruction.getInstruction())).getIndex());
		
		// TODO Auto-generated constructor stub
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


	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		// TODO Auto-generated method stub
		return null;
	}


	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		// TODO Auto-generated method stub
		
	}
	
	/**
	 * @see bytecode.BCInstruction#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula arg0, ExceptionalPostcondition arg1) {
		return null;
	}
}
