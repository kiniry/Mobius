/*
 * Created on Jun 25, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Vector;

import modifexpression.ModifiesExpression;
import modifexpression.ModifiesLocalVariable;
import bcclass.BCMethod;
import bcclass.attributes.ExsuresTable;
import bcclass.attributes.ModifiesSet;
import bcexpression.BCLocalVariable;
import bcexpression.Expression;
import bcexpression.NumberLiteral;
import bytecode.block.Backedge;
import bytecode.branch.BCJumpInstruction;
import constants.BCConstantFieldRef;
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLoopStart extends BCInstruction {
	private BCInstruction loopStartInstruction;

	private Vector backedges ;

	private int number ; 
	// the field shows the number  in the order of loops
	
	// the index in the bytecode where the loop starting with this instruction ends
	private Vector loopEndPositions;

	private Formula invariant;

	// when a terminationmust be proven - and may be decreases is an expression rather  than formula ? 
	private Expression decreases;

	private ModifiesSet modifies;
	
	
	private BCMethod method; 

	//the max. number of iterations this loop may produce
	private int maxIters;
	
	/**
	 * @param _instruction
	 * @param _loopEndPosition
	 */
	public BCLoopStart(BCInstruction _instruction, int _loopEndPosition) {
		loopStartInstruction = _instruction;
		loopEndPositions = new Vector();
		loopEndPositions.add(new Integer( _loopEndPosition));
		instructionHandle = _instruction.getInstructionHandle();
		setNext(_instruction.getNext());
		setPrev(_instruction.getPrev());
		setBCIndex(_instruction.getBCIndex());
		setTargeters(_instruction.getTargeters());
		setBytecode(_instruction.getBytecode());
		setPosition(_instruction.getPosition());

	}

	public String toString() {
		return "LOOPSTART   " + super.toString() + " number " + getLoopIndex();
	}

	/* (non-Javadoc)
		 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
		 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		// calculate  wp of the instruction that is the loop start
		
		Formula  wpInstr = (Formula)_normal_Postcondition.removeAtState(getPosition());
		wpInstr =
			loopStartInstruction.wp(_normal_Postcondition, _exc_Postcondition);
		
		
		Formula  _invariant = (Formula)invariant.copy();
		
		// added to handle the invariants where the values of some locations appear
		_invariant = (Formula)_invariant.removeOldLoop(getPosition() );
			
		// the decreasing term must be >= 0 at the beginning and at the end of the loop
		Formula decreasesWF = new Predicate2Ar( decreases, new NumberLiteral(0), PredicateSymbol.GRTEQ);
	
		Formula invariant_decreseasesWF = Formula.getFormula( (Formula)invariant.copy() , (Formula)decreasesWF.copy() , Connector.AND);
		Formula wp =
			Formula.getFormula(invariant_decreseasesWF, wpInstr, Connector.IMPLIES);
		
		ModifiesExpression[] modifExpr = modifies.getModifiesExpressions();
		Formula assumeStateOfVars = Predicate0Ar.TRUE;
		for (int i = 0; i < modifExpr.length ; i++ ) {
			if (modifExpr[i] == null) {
				continue;
			}
			Formula f = (Formula)modifExpr[i].getPostCondition(getPosition());
			if (modifExpr[i] instanceof ModifiesLocalVariable) {
				BCLocalVariable lVar = ((ModifiesLocalVariable)modifExpr[i]).getLocalVariable();
				wp =  (Formula)wp.substitute( lVar, lVar.atState( getPosition()));				
			} else {
				BCConstantFieldRef fieldRef =  (BCConstantFieldRef)modifExpr[i].getConstantFieldRef();
				wp =  (Formula)wp.substitute( fieldRef, fieldRef.atState( getPosition()));
			}
		}
		wp = Formula.getFormula( (Formula)invariant.copy(), wp,  Connector.AND);
//		 dec >= 0 must be guaranteed by the code before the loop
		wp = Formula.getFormula( (Formula)decreasesWF.copy(), wp, Connector.AND);
		return wp;
		
	}

	/**
	 * @return
	 */
	public Expression getDecreases() {
		return decreases;
	}

	/**
	 * @param formula
	 */
	public void setDecreases(Expression  _decreases) {
		decreases = _decreases;
	}

	public void addLoopEndPosition(int _loopEndPos) {
		if (loopEndPositions == null) {
			loopEndPositions = new Vector();
		}
		loopEndPositions.add(new Integer( _loopEndPos));
	}
	
	/**
	 * @return the position in the bytecode at which
	 * the loop that starts with this instruction ends 
	 */
	public Vector getLoopEndPositions() {
		return loopEndPositions;
	}
	/**
	 * @return
	 */
	public ModifiesSet getModifies() {
		return modifies;
	}

	/**
	 * @param expressions
	 */
	public void setModifies(ModifiesSet modSet) {
		modifies = modSet;
	}

	/**
	 * @return
	 */
	public Formula getInvariant() {
		return invariant;
	}

	/**
	 * @param formula
	 */
	public void setInvariant(Formula formula) {
		invariant = formula;
	}

	/**
	 * @return Returns the method.
	 */
	public BCMethod getMethod() {
		return method;
	}
	/**
	 * @param method The method to set.
	 */
	public void setMethod(BCMethod method) {
		this.method = method;
	}


/**
 * @return Returns the number.
 */
public int getLoopIndex() {
	return number;
}
/**
 * @param number The number to set.
 */
public void setLoopIndex(int number) {
	this.number = number;
}
/**
 * @return Returns the backedges.
 */
public Vector getBackedges() {
	return backedges;
}
/**
 * @param backedges add the backedge 
 */ 
public void addBackedges(Backedge backedge) {
	if (backedges == null) {
		backedges = new Vector();
	}
	backedges.add(backedge);
	
}
/**
 * not used in the application for calculating the calculus. Used for the memory consumption estimation
 * @return
 */
public BCInstruction getWrappedInstruction(){
	return loopStartInstruction;
}

///////////////////////////////////////////////////////////
////////////////Allocation/////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////
//	private int iterationAllocation ;
//	
//	
//
///**
// * @return Returns the iterationAllocation.
// */
//public int getIterationAllocation() {
//	return iterationAllocation;
//}
///**
// * allocations done during an iteration is the difference between what was allocated between the first 
// * and the second entering in the loop 
// * @param iterationAllocation The iterationAllocation to set.
// */
//public void setIterationAllocation(int allocationFromEntryUpToNow) {
//	this.iterationAllocation = allocationFromEntryUpToNow - loopStartInstruction.getAllocate() ;
//}
}
