/*
 * Created on Apr 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.loadstoreinstruction;

import org.apache.bcel.generic.InstructionHandle;

import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLCONST extends BCConstantPUSHInstruction {

	/**
	 * @param _instruction
	 */
	public BCLCONST(InstructionHandle _instruction) {
		super(_instruction);
		setType(JavaType.JavaLONG);
	}

//	/* (non-Javadoc)
//	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
//	 */
//	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition) {
//		Formula wp;
//		wp = _normal_Postcondition.substitute(Expression.getCounter(), Expression.getCounter_plus_1());
//		Stack topStack = new Stack(Expression.getCounter_plus_1());
//		wp = wp.substitute(topStack, getValue());
//		return wp;
//	}

}
