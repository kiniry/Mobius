/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.loadstoreinstruction;


import org.apache.bcel.generic.InstructionHandle;


import bcclass.attributes.ExsuresTable;
import bcexpression.BCLocalVariable;
import bcexpression.Expression;

import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;

import formula.Formula;

/**
 * @author mpavlova
 *
 * Operation: Load reference from local variable
 * 
 * Operand Stack : ... ==> ..., objectref
 * 
 * Description:   The index is an unsigned byte that must be an index into the local variable array of the current frame. 
 * The local variable at index must contain a reference. 
 * The objectref in the local variable at index is pushed onto the operand stack.
 * 
 *  wp = psi^n[t <-- t +1][S(t+1) <-- local(i)]
 */
public  class BCTypeLOAD  extends  BCLocalVariableInstruction{
	//ALOAD,  ILOAD, LLOAD 

	/**
	 * @param _instruction
	 */
	public BCTypeLOAD(InstructionHandle _instruction, BCLocalVariable _lv) {
		super(_instruction, _lv);
		setType((JavaType)_lv.getType());
	}

	

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
//		Util.dump("wp aload psi " + _normal_Postcondition.toString());
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
//		Util.dump("wp aload psi[ t <--- t +1 ] " + wp.toString());
		wp = (Formula)wp.substitute(new Stack( Expression.getCOUNTER_PLUS_1()), getLocalVariable());
//		Util.dump("wp aload = psi[ t <--- t +1 ][s(t+1) <-- index ]  " + wp.toString());
//		if (getPrev() == null) {
//			Util.dump("wp aload " + wp.toString());
//		}
		return wp;
	}

}
