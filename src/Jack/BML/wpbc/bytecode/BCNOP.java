package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;


import formula.Formula;

/**
 * @author Mariela
 *	nop
 *
 * do nothing
 */
public class BCNOP extends BCInstruction {
	
	public BCNOP(InstructionHandle  _instruction) {
		super(_instruction);
	}
	/**
	 * @see bytecode.BCInstruction#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return  _normal_Postcondition ;
	}

	

}
