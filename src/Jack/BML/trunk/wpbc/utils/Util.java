/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package utils;
import org.apache.bcel.generic.MethodGen;

import bcclass.attributes.ExceptionHandler;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bytecode.BCExceptionThrower;

import bytecode.BCInstruction;
import bytecode.EndBlockInstruction;
import bytecode.block.Block;
import bytecode.block.LoopBlock;
import bytecode.branch.BCConditionalBranch;
import bytecode.branch.BCGOTO;
import bytecode.branch.BCJumpInstruction;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Util {
	public static boolean DUMP = true;
	public static BCInstruction[] setTargets(BCInstruction[] _bc, MethodGen _mg) {
		//set possible next instructions for jump instructions -
		for (int i = 0; i < _bc.length; i++) {
			//			if ( _bc[i] instanceof BCExceptionThrower ) {
			//				((BCExceptionThrower)_bc[i]).setExceptionTarget(
			// getExceptionHandlerStarts((BCExceptionThrower)_bc[i], _mg, _bc)
			// );
			//			}
			if (_bc[i] instanceof BCJumpInstruction) {
				BCInstruction _ih = null;
				int offset;
				//dumps the jump instruction
				Util.dump(" setTargets for "
						+ _bc[i].getInstructionHandle().toString());
				offset = ((BCJumpInstruction) _bc[i]).getTargetPosition();
				_ih = getBCInstructionAtPosition(_bc, offset);
				((BCJumpInstruction) _bc[i]).setTarget(_ih);
				_ih.addTargeter(_bc[i]);
			}
		}
		return _bc;
	}
	/**
	 * this method finds the instruction at which the exception handler for the
	 * exception Thrower instruction given as parameter starts.
	 * 
	 * @param _instr-
	 *            the instructiuon for which an exception handler is searched
	 * @param _exc
	 * @param mg
	 *            @param_bc
	 * @return the instruction which is the start for the block that represents
	 *         the exception handler
	 */
	public static BCInstruction getExceptionHandlerStarts(
			BCExceptionThrower _instr, JavaReferenceType _exc, ExceptionHandler[] _excHandles ,
			BCInstruction[] _bc) {
		if (_excHandles == null ) {
			
			return null;
		}
		
		Util.dump("Util.getExceptionHandlerStarts for  " + _exc );
		Util.dump("Util.getExceptionHandlerStarts _excHandles length  " + _excHandles.length );
		BCInstruction _excHandlerStarts = null;
		for (int i = 0; i < _excHandles.length; i++) {
			Util.dump(" excHandle[i] " + _excHandles[i].toString());
			
			if ((_excHandles[i].getStartPC() < _instr
					.getPosition())
					&& (_excHandles[i].getEndPC() > _instr
							.getPosition())) {
				//getCatchType() returns null  if any exception may be
				// managed by this handle
				JavaObjectType _ot = _excHandles[i].getCatchType();
				if ((_ot == null)
						|| (JavaType.subType((JavaObjectType) _exc,
								_ot))) {
					
					_excHandlerStarts = getBCInstructionAtPosition(_bc, _excHandles[i]
							.getHandlerPC());
				}
			}
		}
		return _excHandlerStarts;
	}
	/**
	 * @param i
	 * @return the
	 */
	private static BCInstruction getBCInstructionAtPosition(BCInstruction[] _b,
			int offset) {
		for (int i = 0; i < _b.length; i++) {
			if (_b[i].getPosition() == offset) {
				return _b[i];
			}
		}
		return null;
	}
	public static LoopBlock getLoopBlock(BCInstruction _first,
			BCInstruction _last) {
		LoopBlock _lb = null;
		if (((_last instanceof BCConditionalBranch) || (_last instanceof BCGOTO))
				&& (((BCJumpInstruction) _last).getTarget()
						.getInstructionHandle().equals(_first
						.getInstructionHandle()))) {
			_lb = new LoopBlock(_first, (BCJumpInstruction) _last);
		}
		return _lb;
	}
	public static Block getBlock(BCInstruction _first, BCInstruction _last) {
		Block _b = null;
		//Util.dump("exception trace: " +
		// _last.getInstructionHandle().toString() );
		_b = getLoopBlock(_first, _last);
		if (_b != null) {
			return _b;
		}
		// test was if ( (_last instanceof BCUnconditionalBranch) || (_last
		// instanceof BCReturnInstruction)), as jsr instruction doesnot delimit
		// a block- it detremines a jump to another block
		if (_last instanceof EndBlockInstruction) {
			_b = new Block(_first, _last);
		}
		return _b;
	}
	
	/**
	 * looks for loop starting with _first and end with _last or an instruction
	 * which is next to the _last
	 * 
	 * @param _first -
	 *            loop initial instruction
	 * @param _last -
	 *            instruction that wiol be th end ogf the loop or the end of
	 *            the loop will be next to the _last instruction
	 * @return loop that starts at
	 */
	 
	 
	 
	//TO BE DELETED /here only for test purposes
	public static LoopBlock searchLoopStartingAt(BCInstruction _first,
			BCInstruction _last) {
		LoopBlock _b = null;
		while (_last != null) {
			if ((_last instanceof BCJumpInstruction)
					&& ((BCJumpInstruction) _last).getTarget()
							.getInstructionHandle().equals(
									_first.getInstructionHandle())) {
				_b = getLoopBlock(_first, _last);
			}
			_last = _last.getNext();
		}
		return _b;
	}

	
	/*
	 * public static Vector getBlocks(BCInstruction[] _is) { Vector _b = null;
	 * for (int i = 0; i < _is.length; i++) { if (i ==0) { Vector _v =
	 * getBlocksStartingAt(_is[i]); if (_v == null) { continue; } if (_b ==
	 * null) { _b = new Vector(); } _b.addAll(_v); } if ( _is[i].getTargeters() !=
	 * null ) { Vector _v = getBlocksStartingAt(_is[i] ) ; if (_v == null) {
	 * continue; } if (_b == null) { _b = new Vector(); } _b.addAll(_v); } }
	 * return _b; }
	 */
	public static void dump(String s) {
		if (DUMP) {
			System.out.println(s);
		}
	}
}
