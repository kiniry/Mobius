package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;

import formula.Formula;

/**
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCNOP extends BCInstruction {
	
	public BCNOP(InstructionHandle  _instruction) {
		super(_instruction);
	}
	/**
	 * @see bytecode.BCInstruction#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula arg0, ExceptionalPostcondition arg1) {
		return null;
	}
	//NOP
	

}
