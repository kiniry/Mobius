/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.arithmetic;

import org.apache.bcel.generic.IUSHR;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LUSHR;

import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bcexpression.javatype.JavaType;
import bytecode.BCConstants;
import bytecode.BCInstructionCodes;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeUSHR extends BCArithmeticInstruction {
	
	/**
	 * @param _instruction
	 * @param _type
	 */
	public BCTypeUSHR(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IUSHR) {
			setArithmeticOperation(BCConstants.USHR_INT);
			setInstructionCode(BCInstructionCodes.IUSHR);
		} else if (_instruction.getInstruction() instanceof LUSHR) {
			setArithmeticOperation(BCConstants.USHR_LONG);
			setInstructionCode(BCInstructionCodes.LUSHR);
		}
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}

}