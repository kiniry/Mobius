package bytecode;

import java.util.HashMap;

import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;
import formula.atomic.Predicate;

import utils.FreshIntGenerator;

import bcclass.attributes.ExceptionHandler;
import bcclass.attributes.ExsuresTable;
import bcexpression.EXCEPTIONVariable;
import bcexpression.ref.Reference;

import bcexpression.javatype.JavaObjectType;
import bytecode.block.*;

/**
 * @author M. Pavlova
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public abstract class BCExceptionThrower extends BCInstruction {
	private JavaObjectType[] exceptionsThrown;
	private HashMap excHandleBlocks;

	/**
	 * @param _instruction
	 */
	public BCExceptionThrower(InstructionHandle _instruction) {
		super(_instruction);
	}

	/**
	 * sets the blocks for any corresponding exception (if there exists one)
	 * @param bytecode
	 * @param _excHandlers
	 * @param _trace
	 */
	public void setExceptionTargetBlocks(
		BCInstruction[] bytecode,
		ExceptionHandler[] _excHandlers,
		Trace _trace) {
		if (_excHandlers == null) {
			return;
		}
		if (_excHandlers.length == 0) {
			return;
		}

		for (int k = 0; k < exceptionsThrown.length; k++) {
			for (int i = 0; i < _excHandlers.length; i++) {
				//if the handle i doesnot handle the exception k
				if (!JavaObjectType
					.subType(
						exceptionsThrown[k],
						_excHandlers[i].getCatchType())) {
					continue;
				}
				//if the handle i  handles the exception k
				BCInstruction startInstr =
					bytecode[_excHandlers[i].getStartPC()];
				BCInstruction endInstr = bytecode[_excHandlers[i].getEndPC()];
				Block handleBlock = null;

				//look for this handle block in the trace
				//if it is not still in the trace create it and  add it to the trace 
				if ((handleBlock =
					_trace.getBlockStartingAtEndingAt(startInstr, endInstr))
					== null) {
					handleBlock = new Block(startInstr, endInstr);
//					((EndBlockInstruction)endInstr).setBlock( handleBlock);
					_trace.addBlock(handleBlock);
				}
				if (excHandleBlocks == null) {
					excHandleBlocks = new HashMap();
				}
				excHandleBlocks.put(
					exceptionsThrown[0].getSignature(),
					handleBlock);
				break;
			}
		}
	}

	/**
	 * initialises  the exceptions for this instruction.
	 * Called in the constructor of instructions that are of  type that extend this abstract class 
	 * @param _exceptionsThrown
	 */
	public void setExceptionsThrown(JavaObjectType[] _exceptionsThrown) {
		exceptionsThrown = _exceptionsThrown;
	}

	/**
	 * @return the array of exception types that this instruction may throw
	 */
	public JavaObjectType[] getExceptionsThrown() {
		return exceptionsThrown;
	}

	/** 
	 * @param _exc_type
	 * @return the block that  represents the exception handle for the . 
	 *  Returns null if there is no exception handle for this exception
	 */
	public Block getExceptionHandleBlockForException(JavaObjectType _exc_type) {
		if (excHandleBlocks == null) {
			return null;
		}
		if (excHandleBlocks.size() <= 0) {
			return null;
		}
		Block _b = (Block) excHandleBlocks.get(_exc_type.getSignature());
		return _b;
	}

	/* *
	 * the method returns the postcondition that must  be valid 
	 * after this instruction throws an exception of type _exc_type
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula getWpForException(
		JavaObjectType _exc_type,
		ExsuresTable _exc_post) {
		if ( excHandleBlocks == null) {
			return Predicate._TRUE;
//			return _exc_post.getExcPostconditionFor(_exc_type.getSignature());
		}
		Block block = (Block) excHandleBlocks.get(_exc_type);
		Formula _exc_termination;
		// in case there is no handler for this exception the specified exceptional posctondition must be taken into account
		if (block == null) {
			_exc_termination =
				_exc_post.getExcPostconditionFor(_exc_type.getSignature());
			// make a copy of the postexceptional termination
			Formula _exc_termination_copy = _exc_termination.copy();
			//substitute the object of type of the thrown exception in the formula (if there is a such an object in the exceptional
			// postcondition) 
			_exc_termination_copy.substitute(
				new EXCEPTIONVariable(FreshIntGenerator.getInt(), _exc_type),
				new Reference(FreshIntGenerator.getInt(), _exc_type));
			return _exc_termination_copy;
		}
		//else if there is a handle then the wp of this handler must be taken
		_exc_termination = Predicate._TRUE;//   block.getWp().copy();
		return _exc_termination;
	}
	
}
