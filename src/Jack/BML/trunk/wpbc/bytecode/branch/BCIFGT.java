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
import bcexpression.NumberLiteral;
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
public class BCIFGT extends BCConditionalBranch {

	/**
	 * @param _branchInstruction
	 */
	public BCIFGT(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		// TODO Auto-generated constructor stub
	}
	
	/* (non-Javadoc)
			 * @see bytecode.ByteCode#wp(formula.Formula, specification.Exsures)
			 */
			public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
				Formula wp;
//				Stack stackTop = new Stack(Expression.COUNTER);
		
				//in case of jump - S( t ) > 0
				Formula stackTop_grt_0 = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.GRT);
				Formula grt_branch = getBranchWP();
				grt_branch = grt_branch.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
				Formula wp_stackTop_grt_0 = Formula.getFormula( stackTop_grt_0, grt_branch, Connector.IMPLIES);
		
				// in case of executing next instruction - S( t ) <= 0
				Formula stackTop_not_grt_0 =  new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.LESSEQ);
				Formula not_grt_branch = _normal_Postcondition.substitute(Expression.COUNTER, Expression.COUNTER_MINUS_1);
				Formula wp_stackTop_not_grt_0 = Formula.getFormula( stackTop_not_grt_0, not_grt_branch, Connector.IMPLIES);
		
				wp = Formula.getFormula(wp_stackTop_grt_0, wp_stackTop_not_grt_0, Connector.AND);
				return wp;
			}

}
