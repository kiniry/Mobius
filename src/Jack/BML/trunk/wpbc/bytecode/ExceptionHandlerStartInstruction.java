/*
 * Created on Jul 29, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import bcclass.attributes.ExsuresTable;
import formula.Formula;

/**
 * @author mpavlova
 *
 * Instructions that are starting points for instruction handles 
 * are wrapped in objects of this class. As the wp for this instructions may be calculated more than one time for the same path and the same postcondition the wp for this instruction
 * is saved in the object
 */

// deprecated
public class ExceptionHandlerStartInstruction extends BCInstruction {
	private BCInstruction instruction;
	private Formula wp;
	
	public ExceptionHandlerStartInstruction(BCInstruction _instruction) {
		instruction = _instruction;
		instructionHandle = _instruction.getInstructionHandle();
		setNext(_instruction.getNext());
		setPrev(_instruction.getPrev());
		setBCIndex(_instruction.getBCIndex());
		setTargeters(_instruction.getTargeters());
		//		updateTargets(_instruction.getTargeters());
		setPosition(_instruction.getPosition());

		//actualise the values in the previous and the next instruction
		BCInstruction prev = _instruction.getPrev();
		prev.setNext(this);
		BCInstruction next = _instruction.getNext();
		next.setPrev(this);
	}
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		if (wp != null) {
			return wp;
		}
		Formula _wp = instruction.wp(_normal_Postcondition, _exc_Postcondition);
		return _wp;
	}
	
//	/**
//	 * returns the blocks with which an exceptionHandler may end
//	 * @param excHandlerStart
//	 * @return Vector
//	 */
//	public Vector getExceptionHandlerPaths(Trace _trace) {
//		Block b = _trace.getBlockAt(getPosition());
//		Vector paths = new Vector();
//		_getExceptionHandlerPath(b, null, paths);
//		return paths;
//	}
//	
//	/**
//	 * looks for a path that start with the first instruction of this exception handler
//	 *  
//	 * @param b - the block that is in the path path
//	 * @param path - the current path that is found
//	 * @param paths -  vector of paths that start at  the first instruction of this exception handler
//	 */
//	private void _getExceptionHandlerPath(Block b, Path path, Vector paths) {
//		if (path == null) {
//			path = new Path();
//		}
//		path.addBlockToPath(b);
//		if (b.getLast() instanceof BCTypeRETURN) {
//			if (paths == null) {
//				paths = new Vector();
//			}
//			paths.add(path);
//			return;
//		} else if (b.getLast() instanceof BCATHROW) {
//			if (paths == null) {
//				paths = new Vector();
//			}
//			paths.add(path);
//			return;
//		}
//		if (b instanceof BranchingBlock) {
//			BranchingBlock bb = (BranchingBlock) b;
//			Block branchTarget = bb.getBranchTargetBlock();
//			Path pathCopy = path.copy();
//			_getExceptionHandlerPath(branchTarget, pathCopy, paths);
//			Block seqTarget = bb.getTargetSeqBlock();
//			_getExceptionHandlerPath(seqTarget, path, paths);
//		}  else {
//			Block seqTarget = b.getTargetSeqBlock();
//			_getExceptionHandlerPath(seqTarget, path, paths);
//		}
//	}

//	/**
//	 * initialises the wp for an exception handle over all the possible
//	 * paths in the exec graph that start at the first instruction 
//	 * of excHandler.
//	 * The calculus is different here as over the normal code,as only the paths that start at the first instruction of the exception handler must be considered
//	 * 
//	 * @param Trace _trace,
//	 * @param	Formula _normal_post,
//	 * @param	ExsuresTable exsuresTable
//	 */
//	public void initExcWP(
//		Trace _trace,
//		Formula _normal_post,
//		ExsuresTable exsuresTable) {
//		Formula wp = Predicate.TRUE;
//		Vector paths = getExceptionHandlerPaths(_trace);
//		if (paths == null) {
//			return;
//		}
//		for (int i = 0; i < paths.size(); i++) {
//			Path path = (Path) paths.elementAt(i);
//			Formula _wp = path.wp(_normal_post, exsuresTable);
//			wp = Formula.getFormula(wp, _wp, Connector.AND);
//		}	
//	}

}
