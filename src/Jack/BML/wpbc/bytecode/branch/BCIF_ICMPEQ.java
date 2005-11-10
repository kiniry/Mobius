/*
 * Created on Apr 28, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.branch;

import org.apache.bcel.generic.InstructionHandle;

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
 * if_icmpeq - wp the same as for if_acmpeq
 */
public class BCIF_ICMPEQ extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ICMPEQ(InstructionHandle _branchInstruction) {
		super(_branchInstruction);

	}
	/* (non-Javadoc)
		 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
		 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;

				/////////////////////////////////////////////	
		//top two stack values are not equal
		//S(t)!= S(t-1)
		Formula stackTop_not_equals_stackTop_minus_1 =
		Formula.getFormula(new Predicate2Ar(new Stack(Expression.COUNTER) , new Stack(Expression.getCOUNTER_MINUS_1()) , PredicateSymbol.EQ) 
				, Connector.NOT);

		//psi^n[t <-- t-2]
		Formula not_eq_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());

		//S(t)!= S(t-1) == > psi^n[t <-- t-2]
		wp =
		Formula.getFormula(
				stackTop_not_equals_stackTop_minus_1,
				not_eq_branch,
				Connector.IMPLIES);

		return wp;
	}
	
	
	/* (non-Javadoc)
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {	
		Formula wp;
		///////////////////////////////////////////	
		// top two stack values are equal 
		//S(t)== S(t-1)
		Formula stackTop_equals_stackTop_minus_1 =
			new Predicate2Ar(new Stack(Expression.COUNTER) , new Stack(Expression.getCOUNTER_MINUS_1()) , PredicateSymbol.EQ);
	
		//psi^n[t<-- t-2]
		Formula eq_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
				
		//S(t)== S(t-1) == >  getWPBranch[t<-- t-2]
		wp =
		Formula.getFormula(
				stackTop_equals_stackTop_minus_1,
				eq_branch,
				Connector.IMPLIES);
		
		return wp;
	}

}
