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
 *  if_icmpgt
 */
public class BCIF_ICMPGT extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ICMPGT(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}


	public Formula wp(
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		/////////////////////////////////////////////	
		//top of the stack is not greater than the stack at level top-1
		// S(t-1) <= S(t)
		Formula stackTop_minus_1_not_grt_stackTop =
		new Predicate2Ar(new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER) , PredicateSymbol.LESSEQ);

		//psi^n[t <-- t-2]
		Formula not_grt_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());

		//!( S(t-1) > S(t))== > psi^n[t <-- t-2]
		wp =
		Formula.getFormula(
				stackTop_minus_1_not_grt_stackTop,
				not_grt_branch,
				Connector.IMPLIES);

		return wp;
	}


	/* (non-Javadoc)
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition)  {
		Formula wp;
		// top of the stack is greater than the stack at level top-1
		//S(t-1) > S(t)
		Formula stackTop_minus_1_grt_stackTop =
			new Predicate2Ar(new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER) , PredicateSymbol.GRT);
		

		//getWPBranch[t<-- t-2]
		Formula grt_branch =
		(Formula)_normal_Postcondition.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
		
		//S(t-1) > S(t) == >  getWPBranch[t<-- t-2]
		wp =
		Formula.getFormula(
				stackTop_minus_1_grt_stackTop,
				grt_branch,
				Connector.IMPLIES);
		return wp;
	}


	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		/////////////////////////////////////////////	
		//top of the stack is not greater than the stack at level top-1
		// S(t-1) <= S(t)
		Formula stackTop_minus_1_not_grt_stackTop =
		new Predicate2Ar(new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER) , PredicateSymbol.LESSEQ);

		//psi^n[t <-- t-2]
		vcs.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());

		//!( S(t-1) > S(t))== > psi^n[t <-- t-2]
		Integer key = vcs.addHyp(getPosition(), stackTop_minus_1_not_grt_stackTop );
		vcs.addHypsToVCs( key );
		return vcs;
	}
	
	
	public VCGPath wpBranch(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
//		 top of the stack is greater than the stack at level top-1
		//S(t-1) > S(t)
		Formula stackTop_minus_1_grt_stackTop =
			new Predicate2Ar(new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER) , PredicateSymbol.GRT);
		

		//getWPBranch[t<-- t-2]
		vcs.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_MINUS_2());
		
		//S(t-1) > S(t) == >  getWPBranch[t<-- t-2]
		Integer key  = vcs.addHyp(getPosition(), stackTop_minus_1_grt_stackTop );
		vcs.addHypsToVCs( key );
		return vcs;
	}

}
