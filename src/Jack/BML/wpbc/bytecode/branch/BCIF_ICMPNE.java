/*
 * Created on Apr 29, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;

import org.apache.bcel.generic.InstructionHandle;

import utils.Util;

import bcclass.attributes.ExsuresTable;

import bcexpression.Expression;
import bcexpression.vm.Stack;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

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

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wpNoBranch;
		
		/////////////////////////////////////////////	
		//top two stack values are  equal - no jump
		//S(t)== S(t-1)
		Formula stackTop_eq_stackTop_minus_1 =
			new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				PredicateSymbol.EQ);
		//		Util.dump("wpNotBranch condition " + stackTop_eq_stackTop_minus_1);
		//psi^n[t <-- t-2]
		Formula eq_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());

		//S(t)== S(t-1) == > psi^n[t <-- t-2]
		Formula wp_eq_branch =
			Formula.getFormula(
				stackTop_eq_stackTop_minus_1,
				eq_branch,
				Connector.IMPLIES);

		wpNoBranch = wp_eq_branch;
		return wpNoBranch;
	}

	/* (non-Javadoc)
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(
		Formula _normal_Branch_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wpBranch;
		
		///////////////////////////////////////////	
		// top two stack values are  not equal - comparison succeeds and do a jump
		//S(t)!= S(t-1)

		Formula stackTop_not_eq_stackTop_minus_1 =
			Formula.getFormula( new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				PredicateSymbol.EQ), Connector.NOT );

		//		Util.dump("wpBranch condition " + stackTop_not_eq_stackTop_minus_1);

		//getWPBranch[t<-- t-2]
		Formula not_eq_branch =
		(Formula)_normal_Branch_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
		//S(t)== S(t-1) == >  getWPBranch[t<-- t-2]
		wpBranch =
			Formula.getFormula(
				stackTop_not_eq_stackTop_minus_1,
				not_eq_branch,
				Connector.IMPLIES);
		//		Util.dump("wpBranch for ifcmpne " + wpBranch);

		return wpBranch;

		//		BCInstruction prev = this;
		//		Formula justTest = wpBranch;
		//		while ((prev = prev.getPrev()) != null) {
		//			justTest = prev.wp(justTest, _exc_Postcondition);
		//		}
		//		Util.dump("wp for branch  instr " + justTest);
		//		return justTest;
	}

}
