/*
 * Created on Jun 25, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Vector;

import utils.FreshIntGenerator;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.Variable;
import bcexpression.javatype.JavaType;
import bytecode.branch.BCJumpInstruction;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;
import formula.QuantifiedFormula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLoopStart extends BCInstruction {
	private BCInstruction loopStartInstruction;

	// the index in the bytecode where the loop starting with this instruction ends
	private Vector loopEndPositions;

	private Formula invariant;

	// when a terminationmust be proven - and may be decreases is an expression rather  than formula ? 
	private Formula decreases;

	private Expression[] modifies;

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
		//		updateTargets(_instruction.getTargeters());
		setPosition(_instruction.getPosition());

//		//actualise the values in the previous and the next instruction
//		BCInstruction prev = _instruction.getPrev();
//		prev.setNext(this);
//		BCInstruction next = _instruction.getNext();
//		next.setPrev(this);
	}

	private void updateTargets(Vector targeters) {

		for (int i = 0; i < targeters.size(); i++) {
			BCJumpInstruction jmpInstr =
				(BCJumpInstruction) targeters.elementAt(i);
			jmpInstr.setTarget(this);
		}
	}

	public String toString() {
		return "LOOPSTART   " + super.toString();
	}

	/* (non-Javadoc)
		 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
		 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {

		// calculate  wp of the instruction that is the loop start
		Formula wpInstr =
			loopStartInstruction.wp(_normal_Postcondition, _exc_Postcondition);

		// Invariant ==> wp
		Formula invariant_implies_wp =
			Formula.getFormula((Formula)invariant.copy(), wpInstr, Connector.IMPLIES);

		//if the set of modified expressions for the bytecode that loop is part of is not empty then copy them
		Expression[] modifies1 = null;
		Formula forall_modified_expressions_invariant_implies_wp =
			invariant_implies_wp;
		if ((modifies != null) && (modifies.length > 0)) {
			modifies1 = new Expression[modifies.length];
			//make a copy of every of the modified expressions 
			for (int i = 0; i < modifies.length; i++) {
				//				modifies1[i] = modifies[i].copy();
				modifies1[i] = new Variable(FreshIntGenerator.getInt(), (JavaType)modifies[i].getType());
				forall_modified_expressions_invariant_implies_wp.rename(modifies[i], modifies1[i]);
			}

			//		if the modifies clause of the called method is not empty then quantify 
			//		forall modified( Invariant ==> wp )
			Quantificator[] qunatificators =
				new Quantificator[modifies1.length];
			if ((modifies1 != null) && (modifies1.length > 0)) {
				for (int i = 0; i < modifies1.length; i++) {
					qunatificators[i] =
						new Quantificator(Quantificator.FORALL, modifies1[i]);
				}
				forall_modified_expressions_invariant_implies_wp =
					new QuantifiedFormula(
						forall_modified_expressions_invariant_implies_wp,
						qunatificators);
			}
		}
		Formula wp = null;
		wp =
			Formula.getFormula(
			(Formula)invariant.copy(),
				forall_modified_expressions_invariant_implies_wp,
				Connector.AND);
		return wp;
	}

	/**
	 * @return
	 */
	public Formula getDecreases() {
		return decreases;
	}

	/**
	 * @param formula
	 */
	public void setDecreases(Formula formula) {
		decreases = formula;
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
	public Expression[] getModifies() {
		return modifies;
	}

	/**
	 * @param expressions
	 */
	public void setModifies(Expression[] expressions) {
		modifies = expressions;
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

}
