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
 *  if_acmpeq - branch if the references on the top of the stack are equal
 * 
 * if_acmp<cond> 	branchbyte1 	branchbyte2
 * 
 * Operand Stack :  ..., value1, value2 ==>  ...
 * 
 * Description: Both value1 and value2 must be of type reference. They are both popped from the operand stack and compared. 
 * The comparison succeeds if and only if value1 = value2 . If the comparison succeeds, the unsigned branchbyte1 and branchbyte2
 *  are used to construct a signed 16-bit offset, where the offset is calculated to be (branchbyte1 << 8) | branchbyte2. 
 * Execution then proceeds at that offset from the address of the opcode of this if_acmp<cond> instruction. The target address must be
 *  that of an opcode of an instruction within the method that contains this if_acmp<cond> instruction.
 *  Otherwise, if the comparison fails, execution proceeds at the address of the instruction following this if_acmp<cond> instruction.
 * 
 * S(t) != S(t-1) ==> psi^n[t<-- t-2]
 * &&
 * S(t) == S(t-1) ==> getBranchWp[t<-- t-2]
 */
public class BCIF_ACMPEQ extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIF_ACMPEQ(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
	}

	/**
	 *  this method is called by (exterior) the instructions that are executed after this one
	 *  in case the condition is false and there is not a jump    
	 */ 
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		
		/////////////////////////////////////////////	
		//top two stack values are not equal
		//S(t)!= S(t-1)
		Formula stackTop_not_equals_stackTop_minus_1 = Formula.getFormula( 
				new Predicate2Ar(new Stack(Expression.COUNTER) , new Stack( Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ ) , Connector.NOT);

		//psi^n[t <-- t-2]
		Formula not_eq_branch = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_2());
	
		//S(t)!= S(t-1) == > psi^n[t <-- t-2]
		wp = Formula.getFormula(stackTop_not_equals_stackTop_minus_1, not_eq_branch , Connector.IMPLIES );		
		return wp;
	}


	
	/* (non-Javadoc)
	 * @see bytecode.branch.BCConditionalBranch#wpBranch(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wpBranch(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		// top two stack values are equal - jump
		//S(t)== S(t-1)
		Formula stackTop_equals_stackTop_minus_1 = new Predicate2Ar(new Stack(Expression.COUNTER) , new Stack( Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ );
		
		Formula eq_branch = (Formula)_normal_Postcondition.substitute( Expression.COUNTER, Expression.getCOUNTER_MINUS_2());
		//S(t)== S(t-1) == >  getWPBranch[t<-- t-2]
		wp = Formula.getFormula(stackTop_equals_stackTop_minus_1, eq_branch, Connector.IMPLIES );
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
/////////////////////////////////////////////	
		//top two stack values are not equal
		//S(t)!= S(t-1)
		Formula stackTop_not_equals_stackTop_minus_1 = Formula.getFormula( 
				new Predicate2Ar(new Stack(Expression.COUNTER) , new Stack( Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ ) , Connector.NOT);

		//psi^n[t <-- t-2]
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_2());
	
		//S(t)!= S(t-1) == > psi^n[t <-- t-2]
		Integer key = vcs.addHyp(getPosition(), stackTop_not_equals_stackTop_minus_1);
		vcs.addHypsToVCs( key);
		return vcs;
	}

	public VCGPath wpBranch(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
	
		// top two stack values are equal - jump
		//S(t)== S(t-1)
		Formula stackTop_equals_stackTop_minus_1 = new Predicate2Ar(new Stack(Expression.COUNTER) , new Stack( Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ );
		
		vcs.substitute( Expression.COUNTER, Expression.getCOUNTER_MINUS_2());
		//S(t)== S(t-1) == >  getWPBranch[t<-- t-2]
		Integer key = vcs.addHyp(getPosition(), stackTop_equals_stackTop_minus_1);
		vcs.addHypsToVCs(key);
		return vcs;
	}

}
