package bytecode.objectmanipulation;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;

import specification.ExceptionalPostcondition;

import bcexpression.javatype.JavaType;
import bytecode.BCAllocationInstruction;

/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCNEWARRAY extends BCAllocationInstruction  {

	private JavaType type;
	
	public BCNEWARRAY(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		setType(_type);
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
