/*
 * Created on Apr 28, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.branch;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.NumberLiteral;
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
public class BCIFGE extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIFGE(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;

		// in case of executing next instruction - S(t) < 0
		Formula stackTop_not_geq_0 = new Predicate2Ar(new Stack(
				Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.LESS);
		Formula not_geq_branch = (Formula) _normal_Postcondition.substitute(
				Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		wp = Formula.getFormula(stackTop_not_geq_0, not_geq_branch,
				Connector.IMPLIES);

		return wp;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula,
	 *      bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		// in case of jump - S(t) >= 0
		Formula stackTop_geq_0 = new Predicate2Ar(
				new Stack(Expression.COUNTER), new NumberLiteral(0),
				PredicateSymbol.GRTEQ);
		Formula geq_branch = (Formula) _normal_Postcondition.substitute(
				Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		wp = Formula.getFormula(stackTop_geq_0, geq_branch, Connector.IMPLIES);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		// in case of executing next instruction - S(t) < 0
		Formula stackTop_not_geq_0 = new Predicate2Ar(new Stack(
				Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.LESS);
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());

		Integer key = vcs.addHyp(getPosition(), stackTop_not_geq_0);
		vcs.addHypsToVCs(key);
		return vcs;
	}

	public VCGPath wpBranch(IJml2bConfiguration config, VCGPath vcs,
			ExsuresTable _exc) {
		// in case of jump - S(t) >= 0
		Formula stackTop_geq_0 = new Predicate2Ar(
				new Stack(Expression.COUNTER), new NumberLiteral(0),
				PredicateSymbol.GRTEQ);
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());

		Integer key = vcs.addHyp(getPosition(), stackTop_geq_0);
		vcs.addHypsToVCs(key);
		return vcs;
	}

}
