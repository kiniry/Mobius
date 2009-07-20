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
 * if_acmpne - dual to if_acmpeq
 */
public class BCIF_ACMPNE extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ACMPNE(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;

		////////////////////////////////////////////////////////
		// top two stack values are equal 
		Formula stackTop_equals_stackTop_minus_1 =
			new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				PredicateSymbol.EQ);
		Formula eq_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
		wp =
			Formula.getFormula(
				stackTop_equals_stackTop_minus_1,
				eq_branch,
				Connector.IMPLIES);
		return wp;
	}

	/* (non-Javadoc)
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {

		Formula wp;
		//top two stack values are not equal
		Formula stackTop_not_equals_stackTop_minus_1 =
			Formula.getFormula( new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				PredicateSymbol.EQ) , Connector.NOT);

		Formula not_eq_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
		wp =
			Formula.getFormula(
				stackTop_not_equals_stackTop_minus_1,
				not_eq_branch,
				Connector.IMPLIES);
		return wp;
	}
	
	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
////////////////////////////////////////////////////////
		// top two stack values are equal 
		Formula stackTop_equals_stackTop_minus_1 =
			new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				PredicateSymbol.EQ);
		
		vcs.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
		
		Integer key = vcs.addHyp(getPosition(), stackTop_equals_stackTop_minus_1 );
		vcs.addHypsToVCs( key);

		return vcs;
	}

	public VCGPath wpBranch(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		//top two stack values are not equal
		Formula stackTop_not_equals_stackTop_minus_1 =
			Formula.getFormula( new Predicate2Ar(
				new Stack(Expression.getCOUNTER_MINUS_1()),
				new Stack(Expression.COUNTER),
				PredicateSymbol.EQ) , Connector.NOT);

		vcs.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
		Integer key = vcs.addHyp(getPosition(), stackTop_not_equals_stackTop_minus_1);
		vcs.addHypsToVCs(key);
		return vcs;
	}



}
