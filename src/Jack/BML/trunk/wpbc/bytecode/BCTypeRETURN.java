package bytecode;

import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;


import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.jml.RESULT;
import bcexpression.vm.Stack;
import bytecode.block.*;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeRETURN  extends BCInstruction implements EndBlockInstruction {
	
	/**
	 * @param _instruction
	 */
	public BCTypeRETURN(InstructionHandle _instruction) {
		super(_instruction);
	}
	
	public Formula wp(Formula  _normal_postcondition, ExsuresTable _exs_postcondition) {
		Formula wp;
		Stack stackTop =  new Stack( Expression.COUNTER);
		wp = _normal_postcondition.substitute(new RESULT(), stackTop );
		return wp;
	}
	
	
}
