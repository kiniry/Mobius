/*
 * Created on Apr 29, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.branch;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.Hypothesis;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCIF_ICMPNE extends BCConditionalBranch {
	/**
	 * @param _branchInstruction
	 */
	public BCIF_ICMPNE(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wpNoBranch;

		// ///////////////////////////////////////////
		// top two stack values are equal - no jump
		// S(t)== S(t-1)
		Formula stackTop_eq_stackTop_minus_1 = new Predicate2Ar(new Stack(
				Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ);
		// Util.dump("wpNotBranch condition " + stackTop_eq_stackTop_minus_1);
		// psi^n[t <-- t-2]
		Formula eq_branch = (Formula) _normal_Postcondition.substitute(
				Expression.COUNTER, Expression.getCOUNTER_MINUS_2());

		// S(t)== S(t-1) == > psi^n[t <-- t-2]
		Formula wp_eq_branch = Formula.getFormula(stackTop_eq_stackTop_minus_1,
				eq_branch, Connector.IMPLIES);

		wpNoBranch = wp_eq_branch;
		return wpNoBranch;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula,
	 *      bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(IJml2bConfiguration config,
			Formula _normal_Branch_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wpBranch;

		// /////////////////////////////////////////
		// top two stack values are not equal - comparison succeeds and do a
		// jump
		// S(t)!= S(t-1)

		Formula stackTop_not_eq_stackTop_minus_1 = Formula.getFormula(
				new Predicate2Ar(new Stack(Expression.COUNTER), new Stack(
						Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ),
				Connector.NOT);

		// Util.dump("wpBranch condition " + stackTop_not_eq_stackTop_minus_1);

		// getWPBranch[t<-- t-2]
		Formula not_eq_branch = (Formula) _normal_Branch_Postcondition
				.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_2());
		// S(t)== S(t-1) == > getWPBranch[t<-- t-2]
		wpBranch = Formula.getFormula(stackTop_not_eq_stackTop_minus_1,
				not_eq_branch, Connector.IMPLIES);
		return wpBranch;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		// ///////////////////////////////////////////
		// top two stack values are equal - no jump
		// S(t)== S(t-1)
		Formula stackTop_eq_stackTop_minus_1 = new Predicate2Ar(new Stack(
				Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ);
		// Util.dump("wpNotBranch condition " + stackTop_eq_stackTop_minus_1);
		// psi^n[t <-- t-2]
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_2());

		// S(t)== S(t-1) == > psi^n[t <-- t-2]
		Integer key = vcs.addHyp(getPosition(), stackTop_eq_stackTop_minus_1);
		vcs.addHypsToVCs(key);
		return vcs;
	}

	public VCGPath wpBranch(IJml2bConfiguration config, VCGPath vcs,
			ExsuresTable _exc) {
		// /////////////////////////////////////////
		// top two stack values are not equal - comparison succeeds and do a
		// jump
		// S(t)!= S(t-1)

		Formula stackTop_not_eq_stackTop_minus_1 = Formula.getFormula(
				new Predicate2Ar(new Stack(Expression.COUNTER), new Stack(
						Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ),
				Connector.NOT);

		// Util.dump("wpBranch condition " + stackTop_not_eq_stackTop_minus_1);

		// getWPBranch[t<-- t-2]
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_2());
		// S(t)== S(t-1) == > getWPBranch[t<-- t-2]

		Integer key = vcs.addHyp(getPosition(),
				stackTop_not_eq_stackTop_minus_1);
		vcs.addHypsToVCs(key);
		return vcs;

	}

}
