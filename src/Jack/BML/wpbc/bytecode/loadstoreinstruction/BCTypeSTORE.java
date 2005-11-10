/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.loadstoreinstruction;

import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bcexpression.BCLocalVariable;
import bcexpression.Expression;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;


/**
 * @author mpavlova
 *
 * Operation: Store the stack top  into local variable
 * 
 * Format : astore index 	
 * 
 * Operand Stack:   ..., objectref ==> ...
 * 
 * wp = psi^n[t < -- t -1][o ==local(index)  <-- S( t)] 
 */
public class BCTypeSTORE extends BCLocalVariableInstruction {
	//ASTORE, ISTORE, LSTORE
	
	/**
	 * @param _instruction
	 */
	public BCTypeSTORE(InstructionHandle _instruction, BCLocalVariable _lv) {
		super(_instruction, _lv);
		setType((JavaType)_lv.getType());
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		wp = (Formula)wp.substitute(getLocalVariable(),  new Stack(Expression.COUNTER) );
		return wp;
	}
}
