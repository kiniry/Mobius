/*
 * Created on Jun 25, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import bcclass.BCMethod;
import bcclass.attributes.ExsuresTable;
import bcclass.attributes.ModifiesSet;
import bcexpression.Expression;
import bytecode.branch.BCConditionalBranch;
import formula.Connector;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLoopEnd extends BCInstruction {
	
	BCInstruction loopEndInstruction;
	
	private Formula invariant;
	
	// when a terminationmust be proven - and may be decreases is an expression rather  than formula ? 
	private Expression decreases;
	private ModifiesSet modifies;
	
	/**
	 * the index in the bytecode at which the loop that ends with thisinstruction starts
	 */
	private int loopStartPosition;
	
	private BCMethod method;
	
	/**
	 * @param _instruction
	 * @param _loopStartPosition
	 */
	public BCLoopEnd(BCInstruction _instruction, int _loopStartPosition) {
		loopEndInstruction = _instruction; 
		loopStartPosition = _loopStartPosition;
		instructionHandle = _instruction.getInstructionHandle();
		setNext( _instruction.getNext());
		setPrev( _instruction.getPrev());
		setBCIndex(_instruction.getBCIndex());
		setTargeters( _instruction.getTargeters() );
		setPosition( _instruction.getPosition());
//		setAssert( _instruction.getAssert());

		//actualise the values in the previous and the next instruction
//		BCInstruction prev = _instruction.getPrev();
//		prev.setNext(this);
//		BCInstruction next = _instruction.getNext();
//		next.setPrev( this );
	
	}
	
	public BCInstruction getWrappedInstruction() {
		return loopEndInstruction;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
//			Formula  normal_Post = Formula.getFormula(_normal_Postcondition, invariant, Connector.AND);
			Formula wp = loopEndInstruction.wp( _normal_Postcondition, _exc_Postcondition);
			wp = (Formula)wp.atState(getBCIndex() );
			Formula vectorStateAtThisInstruction = method.getStateVectorAtInstr( getBCIndex(), modifies);
			wp = Formula.getFormula(wp, vectorStateAtThisInstruction, Connector.AND);
			return wp;
	}
	
	public Formula wpBranch(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
//			Formula  normal_Post = Formula.getFormula(_normal_Postcondition, invariant, Connector.AND);
			Formula wp = ((BCConditionalBranch)loopEndInstruction).wpBranch( _normal_Postcondition, _exc_Postcondition);
			wp = (Formula)wp.atState(getBCIndex() );
			Formula vectorStateAtThisInstruction = method.getStateVectorAtInstr( getBCIndex(), modifies);
			wp = Formula.getFormula(wp, vectorStateAtThisInstruction, Connector.AND);
			return wp;
	}
	
	public String toString() {
		return "LOOPEND :  "  + super.toString();
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
	public void setDecreases(Expression expression) {
		decreases = expression;
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
	 * @param modifies The modifies to set.
	 */
	public void setModifies(ModifiesSet modifies) {
		this.modifies = modifies;
	}
}
