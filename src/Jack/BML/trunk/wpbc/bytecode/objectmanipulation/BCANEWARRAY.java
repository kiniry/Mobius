package bytecode.objectmanipulation;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;
import specification.ExceptionalPostcondition;

import formula.Formula;

import bcexpression.javatype.JavaType;
import bytecode.BCAllocationInstruction;
import bytecode.objectmanipulation.*;

/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCANEWARRAY extends BCAllocationInstruction implements BCCPInstruction  {
	private int index;
	private JavaType type;
	public BCANEWARRAY(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		setIndex( ( (CPInstruction)_instruction.getInstruction()).getIndex());
		setType(_type);
	}

		/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		index = _index;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#getIndex()
	 */
	public int getIndex() {
		return index;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		type = _type;
	}
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}
}
