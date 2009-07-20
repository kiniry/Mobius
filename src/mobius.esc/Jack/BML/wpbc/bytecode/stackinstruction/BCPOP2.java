/*
 * Created on Apr 21, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.stackinstruction;

import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bytecode.BCInstruction;

/**
 * @author mpavlova
 *
 *  pop2
 * 
 *  Operation: Pop the top one or two operand stack values
 *
 * Format:  pop2 	
 * 
 * Operand Stack
 *
 * Form 1: ..., value2, value1 == >...
 *  where each of value1 and value2 is a value of a category 1 computational type (?3.11.1).
 *
 *   Form 2: ..., value ==>...
 *   where value is a value of a category 2 computational type  
 *
 * NB: we consider only types of computational type 1
 * 
 * 
 * wp = psi^n[t<--t-2]
 */
public class BCPOP2  extends BCInstruction implements BCStackInstruction{

	/**
	 * @param _instruction
	 */
	public BCPOP2(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_2());
		return wp;
	}

}
