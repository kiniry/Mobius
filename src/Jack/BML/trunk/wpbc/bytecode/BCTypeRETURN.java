package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.vm.Stack;


import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeRETURN
	extends BCInstruction {
//	private Block blockEndingWithThis;

	/**
	 * @param _instruction
	 */
	public BCTypeRETURN(InstructionHandle _instruction) {
		super(_instruction);
	}

//	public void setBlock(Block block) {
//		blockEndingWithThis = block;
//	}

	public Formula wp(
		Formula _normal_postcondition,
		ExsuresTable _exs_postcondition) {
		Formula wp;
		Stack stackTop = new Stack(Expression.COUNTER);
		wp = (Formula)_normal_postcondition.substitute(Expression._RESULT, stackTop);
//		Util.dump("wp return " + wp.toString());
		return wp;
	}

//	/* (non-Javadoc)
//	 * @see bytecode.EndBlockInstruction#calculateRecursively()
//	 */
//	public Formula calculateRecursively(
//		Formula _normal_postcondition,
//		ExsuresTable _exs_postcondition) {
//		Formula wp =
//			blockEndingWithThis.calculateRecursively(
//				_normal_postcondition,
//				_exs_postcondition);
//		return wp;
//	}

}
