/*
 * Created on Jun 25, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.BCMethod;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcclass.attributes.ModifiesSet;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bytecode.branch.BCConditionalBranch;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.modifexpression.ModifiesArray;
import bytecode_wp.modifexpression.ModifiesDOT;
import bytecode_wp.modifexpression.ModifiesExpression;
import bytecode_wp.modifexpression.ModifiesIdent;
import bytecode_wp.modifexpression.ModifiesLocalVariable;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLoopEnd extends BCInstruction {

	BCInstruction loopEndInstruction;

	private Formula invariant;

	// when a terminationmust be proven - and may be decreases is an expression
	// rather than formula ?
	private Expression decreases;

	private ModifiesSet modifies;

	/**
	 * the index in the bytecode at which the loop that ends with
	 * thisinstruction starts
	 */
	private int loopEntry;

	private BCMethod method;

	private BCInstruction[] bytecode;

	/**
	 * @param _instruction
	 * @param _loopStartPosition
	 */
	public BCLoopEnd(BCInstruction _instruction, int _loopStartPosition) {
		loopEndInstruction = _instruction;
		loopEntry = _loopStartPosition;
		instructionHandle = _instruction.getInstructionHandle();
		setBytecode(_instruction.getBytecode());
		setNext(_instruction.getNext());
		setPrev(_instruction.getPrev());
		setBCIndex(_instruction.getBCIndex());
		setTargeters(_instruction.getTargeters());
		setPosition(_instruction.getPosition());
		// setAssert( _instruction.getAssert());

		// actualise the values in the previous and the next instruction
		// BCInstruction prev = _instruction.getPrev();
		// prev.setNext(this);
		// BCInstruction next = _instruction.getNext();
		// next.setPrev( this );

	}

	public BCInstruction getWrappedInstruction() {
		return loopEndInstruction;
	}

	/**
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      bcclass.attributes.ExsuresTable)
	 * @deprecated
	 * 
	 * forall fields (f ) f==f_at_loop_end ==> Invariant[f <- f_at_loop_end] /\
	 * f == f_at_start_loop
	 */
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		VCGPath wp = _wp(config, vcs, _exc);
		
		if (!(loopEndInstruction instanceof BCConditionalBranch)) {
			wp = loopEndInstruction.wp(config, wp, _exc);
		} else if (((BCConditionalBranch) loopEndInstruction).getTarget() == null
				) {
			wp = ((BCConditionalBranch) loopEndInstruction).wpBranch(config,
					wp, _exc);
		} else {
			wp = ((BCConditionalBranch) loopEndInstruction)
					.wp(config, wp, _exc);
		} 
		return wp;
	}

	/**
	 * this methods verifies adds verification conditions for the modifies
	 * clause and quantifies over the variables
	 * 
	 * @param vcs
	 * @param _exc_Postcondition
	 * @return
	 */
	private VCGPath _wp(IJml2bConfiguration config,VCGPath vcs, ExsuresTable _exc_Postcondition) {
		// loop variant - check for termination
		if (decreases.equals(new NumberLiteral(1))) {
			return vcs;
		}
		Expression decreasesCopy = decreases.copy();
		Expression decreasesAtLoopStart = decreases.copy();
		decreasesAtLoopStart = atStateDec(config, decreasesAtLoopStart, loopEntry);

		Predicate2Ar terminationConditionDecreases = new Predicate2Ar(
				decreasesCopy, decreasesAtLoopStart,
				PredicateSymbol.LESS);

	
		vcs.addGoal(VcType.LOOP_TERMINATION, terminationConditionDecreases);
		
		return vcs;
	}
	/**
	 * the method "freezes" the expressions in the decrease statement
	 * @param config
	 * @param dec
	 * @return
	 */
	private Expression atStateDec(IJml2bConfiguration config, Expression dec, int loopEntry) {
		ModifiesExpression[] modifExpr = modifies.getModifiesExpressions();
		for (int i = 0; i < modifExpr.length; i++) {
			if (modifExpr[i] == null) {
				continue;
			}
			
			if (modifExpr[i] instanceof ModifiesLocalVariable) {
				BCLocalVariable lVar = ((ModifiesLocalVariable) modifExpr[i])
						.getLocalVariable();

				dec =  dec.atState(loopEntry, lVar);
			} else if (modifExpr[i] instanceof ModifiesDOT) {
				Expression modified = modifExpr[i].getExpressionModifies();
				dec = dec.atState(loopEntry , modified);

				
			} else if (modifExpr[i] instanceof ModifiesIdent) {
				Expression modified = modifExpr[i].getExpressionModifies();
				/* Expression atState = modified.atState(getPosition()); */
				dec = dec.atState(loopEntry, modified);
				
			} else if (modifExpr[i] instanceof ModifiesArray) {
				Expression modified = modifExpr[i].getModifies();
				// Expression modified = modifExpr[i].getExpressionModifies();
				// Expression atState = modified.atState(getPosition());
				dec = dec
						.loopModifArrayAtState(loopEntry, modified);
				
			}
		}
		return dec;
	}
	
	
	public String toString() {
		return "LOOPEND :  " + super.toString();
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
	 * @param method
	 *            The method to set.
	 */
	public void setMethod(BCMethod method) {
		this.method = method;
	}

	/**
	 * @param modifies
	 *            The modifies to set.
	 */
	public void setModifies(ModifiesSet modifies) {
		this.modifies = modifies;
	}

	/**
	 * @return Returns the loopStartPosition.
	 */
	public int getLoopEntry() {
		return loopEntry;
	}

}
