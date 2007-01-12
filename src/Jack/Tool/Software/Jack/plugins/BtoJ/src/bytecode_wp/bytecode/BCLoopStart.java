/*
 * Created on Jun 25, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcclass.attributes.ModifiesSet;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bytecode.block.Backedge;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.modifexpression.ModifiesArray;
import bytecode_wp.modifexpression.ModifiesDOT;
import bytecode_wp.modifexpression.ModifiesExpression;
import bytecode_wp.modifexpression.ModifiesIdent;
import bytecode_wp.modifexpression.ModifiesLocalVariable;
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLoopStart extends BCInstruction {
	private BCInstruction loopStartInstruction;

	private Vector backedges;

	private int number;

	// the field shows the number in the order of loops

	// the index in the bytecode where the loop starting with this instruction
	// ends
	private Vector loopEndPositions;

	private Formula invariant;

	// prove loop termination - and may be decreases is an expression rather
	// than formula ?
	private Expression decreases;

	private ModifiesSet modifies;

	private BCMethod method;



	private boolean checkInit = false;


	/**
	 * @param _instruction
	 * @param _loopEndPosition
	 */
	public BCLoopStart(BCInstruction _instruction, int _loopEndPosition) {
		loopStartInstruction = _instruction;
		loopEndPositions = new Vector();
		loopEndPositions.add(new Integer(_loopEndPosition));
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      bcclass.attributes.ExsuresTable)
	 */
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		// calculate wp of the instruction that is the loop start
		Formula wp = loopStartInstruction.wp(config, _normal_Postcondition,
				_exc_Postcondition);

		// the decreasing term must be >= 0 at the beginning and at the end of
		// the loop
		Formula decreasesWF = getDecreases();
		Formula inv = (Formula) invariant.copy();
		Formula invariant_decreseasesWF = Formula.getFormula(inv,
				(Formula) decreasesWF.copy(), Connector.AND);
		wp = Formula.getFormula(invariant_decreseasesWF, wp, Connector.IMPLIES);

		// hypothesis about the locations - take into account the modifies
		// clause of the loop
		Formula vectorOfFieldToAssume = Predicate0Ar.TRUE;

		ModifiesExpression[] modifExpr = modifies.getModifiesExpressions();
		for (int i = 0; i < modifExpr.length; i++) {
			if (modifExpr[i] == null) {
				continue;
			}
			Formula f = (Formula) modifExpr[i].getPostCondition(config,
					getPosition());

			if (modifExpr[i] instanceof ModifiesLocalVariable) {
				BCLocalVariable lVar = ((ModifiesLocalVariable) modifExpr[i])
						.getLocalVariable();

				wp = (Formula) wp.atState(getPosition(), lVar);

				vectorOfFieldToAssume = Formula.getFormula(
						vectorOfFieldToAssume, f, Connector.AND);

			} else if (modifExpr[i] instanceof ModifiesDOT) {
				Expression modified = modifExpr[i].getExpressionModifies();
				wp = (Formula) wp.atState(getPosition(), modified);

				vectorOfFieldToAssume = Formula.getFormula(
						vectorOfFieldToAssume, f, Connector.AND);
			} else if (modifExpr[i] instanceof ModifiesIdent) {
				Expression modified = modifExpr[i].getExpressionModifies();
				/* Expression atState = modified.atState(getPosition()); */
				wp = (Formula) wp.atState(getPosition(), modified);
				vectorOfFieldToAssume = Formula.getFormula(
						vectorOfFieldToAssume, f, Connector.AND);
			} else if (modifExpr[i] instanceof ModifiesArray) {
				Expression modified = modifExpr[i].getModifies();
				// Expression modified = modifExpr[i].getExpressionModifies();
				// Expression atState = modified.atState(getPosition());
				wp = (Formula) wp
						.loopModifArrayAtState(getPosition(), modified);
				vectorOfFieldToAssume = Formula.getFormula(
						vectorOfFieldToAssume, f, Connector.AND);
			}

		}

		wp = Formula.getFormula(vectorOfFieldToAssume, wp, Connector.IMPLIES);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs,
			ExsuresTable _exc_Postcondition) {
		// calculate wp of the instruction that is the loop start
		VCGPath wp = loopStartInstruction.wp(config, vcs, _exc_Postcondition);

		// the decreasing term must be >= 0 at the beginning and at the end of
		// the loop
		Formula decreasesWF = getDecreases();
		Formula inv = null;
		if (invariant == null) {
			inv = Predicate0Ar.TRUE;
		} else {
			inv = (Formula) invariant.copy();

		}
		// add as
		Integer key1 = wp.addHyp(getPosition(), inv);
		wp.addHypsToVCs(key1);
		// if this is not the default value of decreases 
		
		Integer key2 = wp.addHyp(getPosition(), decreasesWF);
		wp.addHypsToVCs(key2);
		
		// wp = Formula.getFormula(invariant_decreseasesWF, wp,
		// Connector.IMPLIES);

		// hypothesis about the locations - take into account the modifies
		// clause of the loop
		Vector vectorOfFieldToAssume = null;
		//if (modifies != null) {
			vectorOfFieldToAssume = new Vector();
			ModifiesExpression[] modifExpr = modifies.getModifiesExpressions();
			for (int i = 0; i < modifExpr.length; i++) {
				if (modifExpr[i] == null) {
					continue;
				}
				Formula f = (Formula) modifExpr[i].getPostCondition(config,
						getPosition());

				if (modifExpr[i] instanceof ModifiesLocalVariable) {
					BCLocalVariable lVar = ((ModifiesLocalVariable) modifExpr[i])
							.getLocalVariable();
					wp.atState(getPosition(), lVar);
				} else if (modifExpr[i] instanceof ModifiesDOT) {
					Expression modified = modifExpr[i].getExpressionModifies();
					wp.atState(getPosition(), modified);
				} else if (modifExpr[i] instanceof ModifiesIdent) {
					Expression modified = modifExpr[i].getExpressionModifies();
					/* Expression atState = modified.atState(getPosition()); */
					wp.atState(getPosition(), modified);
				} else if (modifExpr[i] instanceof ModifiesArray) {
					Expression modified = ((ModifiesArray) modifExpr[i])
							.getArray();

					wp.loopModifArrayAtState(getPosition(), modified);
					// wp.atState(getPosition(), modified);
				}
				vectorOfFieldToAssume.add(f);
			}
		//}
		if (vectorOfFieldToAssume != null) {
			// add the quantification over the modified variables
			for (int i = 0; i < vectorOfFieldToAssume.size(); i++) {
				Formula f = (Formula) vectorOfFieldToAssume.elementAt(i);
				Integer key = wp.addHyp(getPosition(), f);
				wp.addHypsToVCs(key);
			}
		}
		//add verification condition for the invariant initialization
		if (!checkInit) {
			checkInit = true;
			wp.addGoal(VcType.LOOPINIT, (Formula) invariant.copy());
			wp.addGoal(VcType.LOOPINIT, (Formula) getDecreases().copy());
		}
		return wp;
	}

	/**
	 * @return formula that asserts that the decreasing expression is bigger or
	 *         equal to 0
	 */
	public Formula getDecreases() {
		if (decreases == null) {
			return Predicate0Ar.TRUE;
		}
		return new Predicate2Ar(decreases.copy(), new NumberLiteral(0),
				PredicateSymbol.GRTEQ);

	}

	/**
	 * @param formula
	 */
	public void setDecreases(Expression _decreases) {
		decreases = _decreases;
	}

	public void addLoopEndPosition(int _loopEndPos) {
		if (loopEndPositions == null) {
			loopEndPositions = new Vector();
		}
		loopEndPositions.add(new Integer(_loopEndPos));
	}

	/**
	 * @return the position in the bytecode at which the loop that starts with
	 *         this instruction ends
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
	 * @param method
	 *            The method to set.
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
	 * @param number
	 *            The number to set.
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
	 * @param backedges
	 *            add the backedge
	 */
	public void addBackedges(Backedge backedge) {
		if (backedges == null) {
			backedges = new Vector();
		}
		backedges.add(backedge);

	}

	/**
	 * not used in the application for calculating the calculus. Used for the
	 * memory consumption estimation
	 * 
	 * @return
	 */
	public BCInstruction getWrappedInstruction() {
		return loopStartInstruction;
	}

	// /////////////////////////////////////////////////////////
	// //////////////Allocation/////////////////////////////////////////////////////////
	// /////////////////////////////////////////////////////////
	// private int iterationAllocation ;
	//	
	//	
	//
	// /**
	// * @return Returns the iterationAllocation.
	// */
	// public int getIterationAllocation() {
	// return iterationAllocation;
	// }
	// /**
	// * allocations done during an iteration is the difference between what was
	// allocated between the first
	// * and the second entering in the loop
	// * @param iterationAllocation The iterationAllocation to set.
	// */
	
	////////////////////////////////////////////////////////////////////
	////////////////ANNOTATION FOR MEMORY CONSUMPTIONS/////////////////
	////////////////////////////////////////////////////////////////////
	// the max. number of iterations this loop may produce
	private int maxIters;
	private int iterationAllocation = -1;
	private boolean startToCalculate = false;
	
	
	public void setIterationAllocation(int consum) {
	    this.iterationAllocation = consum;
	}
	
	public int getIterationAllocation() {
		return iterationAllocation;
	}

	public boolean isStartToCalculate() {
		return startToCalculate;
	}

	public void setStartToCalculate(boolean startToCalculate) {
		this.startToCalculate = startToCalculate;
	}
	
}
