/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.ConstantPushInstruction;
import org.apache.bcel.generic.InstructionHandle;
import specification.ExceptionalPostcondition;
import formula.Formula;
import bcexpression.Expression;
import bcexpression.NumberLiteral;

/**
 * @author mpavlova
 *
 * Denotes a push instruction that produces a literal on the stack : BIPUSH, DCONST, FCONST, ICONST, LCONST, SIPUSH
 */
public class BCConstantPUSHInstruction extends BCInstruction {
	//    BIPUSH, DCONST, FCONST, ICONST, LCONST, SIPUSH
	
	NumberLiteral value; 
	/**
	 * @param _instruction
	 */
	public BCConstantPUSHInstruction(InstructionHandle _instruction) {
		super(_instruction);
		ConstantPushInstruction cp = (ConstantPushInstruction)_instruction.getInstruction();
		setValue(cp.getValue());
	}
	
	private void setValue(Number _value) {
		value = new NumberLiteral(_value);
	} 

	public Expression getValue() {
		return null;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}
}
