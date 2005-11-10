/*
 * Created on Apr 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.loadstoreinstruction;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCInstruction;
import bytecode.BCTypedInstruction;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCACONST_NULL extends BCInstruction implements
BCTypedInstruction {
	
	/**
	 * @param _instruction
	 */
	public BCACONST_NULL(InstructionHandle _instruction) {
		super(_instruction);
		setType(JavaType.JavaNULL);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		wp =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_PLUS_1());
		//Stack topStack_plus_1 = new Stack(Expression.COUNTER_PLUS_1);
		wp = (Formula)wp.substitute(new Stack(Expression.getCOUNTER_PLUS_1()) ,Expression._NULL);
		return wp;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaNULL;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
	}

}
