/*
 * Created on Jun 25, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import modifexpression.ModifiesExpression;
import modifexpression.ModifiesLocalVariable;
import constants.BCConstantFieldRef;
import bcclass.BCMethod;
import bcclass.attributes.ExsuresTable;
import bcclass.attributes.ModifiesSet;
import bcexpression.BCLocalVariable;
import bcexpression.Expression;
import bcexpression.NumberLiteral;
import bytecode.branch.BCConditionalBranch;
import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLoopEnd extends BCInstruction {
	
	BCInstruction loopEndInstruction;
	
	private Formula invariant;
	
	// when a terminationmust be proven - and may be decreases is an expression rather  than formula ? 
	private Expression decreases;
	private ModifiesSet modifies;
	
	/**
	 * the index in the bytecode at which the loop that ends with thisinstruction starts
	 */
	private int loopStartPosition;
	
	private BCMethod method;
	
	private BCInstruction[] bytecode;
	
	/**
	 * @param _instruction
	 * @param _loopStartPosition
	 */
	public BCLoopEnd(BCInstruction _instruction, int _loopStartPosition) {
		loopEndInstruction = _instruction; 
		loopStartPosition = _loopStartPosition;
		instructionHandle = _instruction.getInstructionHandle();
		setBytecode(_instruction.getBytecode());
		setNext( _instruction.getNext());
		setPrev( _instruction.getPrev());
		setBCIndex(_instruction.getBCIndex());
		setTargeters( _instruction.getTargeters() );
		setPosition( _instruction.getPosition());
//		setAssert( _instruction.getAssert());

		//actualise the values in the previous and the next instruction
//		BCInstruction prev = _instruction.getPrev();
//		prev.setNext(this);
//		BCInstruction next = _instruction.getNext();
//		next.setPrev( this );
	
	}
	
	public BCInstruction getWrappedInstruction() {
		return loopEndInstruction;
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 * 
	 * forall fields (f ) f==f_at_loop_end ==> Invariant[f <- f_at_loop_end] /\ f == f_at_start_loop 
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
			Formula wp =  _wp(_normal_Postcondition, _exc_Postcondition);
			wp = loopEndInstruction.wp( wp, _exc_Postcondition);
			
			return wp;			
	}
	
	public Formula wpBranch(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
//		Formula  normal_Post = Formula.getFormula(invariant, _normal_Postcondition, Connector.IMPLIES);
		Formula wp = _wp(_normal_Postcondition, _exc_Postcondition);
		wp = ((BCConditionalBranch)loopEndInstruction).wpBranch( wp, _exc_Postcondition);
		
		return wp;
	}
	
	/**
	 * this methods verifies adds verification conditions for the 
	 * modifies clause and quantifies over the variables 
	 * @param wp
	 * @param _exc_Postcondition
	 * @return
	 */
	private Formula _wp(Formula wp, ExsuresTable _exc_Postcondition) {
	/*	wp = (Formula)wp.atState(getPosition() );*/
		//forall fields (f ) f==f_at_loop_end /\ forall i : locVar index.  loc(i) = loc_at_start_end
		Formula localVarStateAssume = Predicate0Ar.TRUE;
		Formula  vectorOfFieldToAssume = Predicate0Ar.TRUE;
	
		ModifiesExpression[] modifExpr = modifies.getModifiesExpressions();
		for (int i = 0; i < modifExpr.length ; i++ ) {
			if (modifExpr[i] == null) {
				continue;
			}
			Formula f = (Formula)modifExpr[i].getPostCondition(getPosition());
			if (modifExpr[i] instanceof ModifiesLocalVariable) {
				BCLocalVariable lVar = ((ModifiesLocalVariable)modifExpr[i]).getLocalVariable();
				wp =  (Formula)wp.substitute( lVar, lVar.atState( getPosition()));
				vectorOfFieldToAssume  = Formula.getFormula(vectorOfFieldToAssume, f, Connector.AND);
				
			} else {
				BCConstantFieldRef fieldRef =  (BCConstantFieldRef)modifExpr[i].getConstantFieldRef();
				wp =  (Formula)wp.substitute( fieldRef, fieldRef.atState( getPosition()));
				vectorOfFieldToAssume  = Formula.getFormula(vectorOfFieldToAssume, f, Connector.AND);
			}
		}
		
		// termination
		Expression decreasesCopy = decreases.copy();
		Expression decreasesAtLoopStart = decreases.copy() ;
		decreasesAtLoopStart = decreasesAtLoopStart.atState(loopStartPosition);
		
		Predicate2Ar terminationConditionDecreases = new Predicate2Ar( decreasesCopy.copy(), decreasesAtLoopStart,  PredicateSymbol.LESS);
		Predicate2Ar terminationWF =  new Predicate2Ar(decreasesCopy, new NumberLiteral(0), PredicateSymbol.GRTEQ );
		Formula terminationCondition = Formula.getFormula( terminationConditionDecreases, terminationWF, Connector.AND);
//		 NB : with loop_end_state
		Formula vectorStateAssumption = Formula.getFormula( localVarStateAssume, vectorOfFieldToAssume, Connector.AND);
		
		//forall fields (f ) f =f_at_start_loop /\ forall i : locVar index.  loc(i) = loc_at_start_loop
		
		//commented 
 		/*Formula varsNotChanged = method.getVectorAtStateToHold( loopStartPosition, modifies);*/
		
		Formula varsNotChanged = method.getVectorAtStateToHold( loopStartPosition, modifies);
 		// wp for invariant and modifies correctness
		wp = Formula.getFormula( wp , varsNotChanged, Connector.AND );
		
		// and alsoi terminatiopn cotrrectness
		wp = Formula.getFormula( wp, terminationCondition, Connector.AND);
		
		// NB : with loop_end_state
		wp = Formula.getFormula( vectorStateAssumption, wp, Connector.IMPLIES);
		
		/*wp = Formula.getFormula( vectorStateAssumption,wp,  Connector.IMPLIES);*/
		
		return wp;
	} 
	
	
	public String toString() {
		return "LOOPEND :  "  + super.toString();
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
	 * @param method The method to set.
	 */
	public void setMethod(BCMethod method) {
		this.method = method;
	}
	/**
	 * @param modifies The modifies to set.
	 */
	public void setModifies(ModifiesSet modifies) {
		this.modifies = modifies;
	}
}
