package bytecode;


import org.apache.bcel.generic.InstructionHandle;
import specification.ExceptionalPostcondition;

import formula.Formula;

import bcexpression.javatype.JavaType;
/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCDCMPL extends BCInstruction implements BCTypedInstruction{
	
	/**
	 * @param _instruction
	 */
	public BCDCMPL(InstructionHandle _instruction) {
		super(_instruction);

	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaDOUBLE;
	}

	/* (non-Javadoc)
	 * does nothing as the type of this instruction is by default long
	 * @see bytecode.BCTypedInstruction#setType(org.apache.bcel.generic.TypedInstruction, org.apache.bcel.generic.ConstantPoolGen)
	 */
	public void setType(JavaType _type) {
		
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}

}

