/*
 * Created on Feb 21, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.memory.allocation;

import java.util.Vector;

import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcclass.attributes.ModifiesSet;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.jml.OLD_LOOP;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCLoopEnd;
import bytecode_wp.bytecode.BCLoopStart;
import bytecode_wp.bytecode.objectmanipulation.BCNEW;
import bytecode_wp.constants.MemUsedConstant;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.modifexpression.ModifiesExpression;
import bytecode_wp.modifexpression.ModifiesIdent;
import bytecode_wp.modifexpression.ModifiesLocalVariable;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class BCInstructionAlloc {
	BCInstruction bcInstr;
	private boolean checked = false;
	
	//////////////////////////////////////////////////////////////////
	//////// if the instruction is detected to be a start of a loop///
	//////////////////////////////////////////////////////////////////
	private int maxIter = 3 ;
	private int loopConsumption;
	// the condition that guarantees loop termination
	private Expression decreases;
	
	// the variable that changes on every iteration - participates in the 
	// decreases expression
	private Expression variant;
	
	///////////////////////////////
	
	public BCInstructionAlloc(BCInstruction instr ) {
		bcInstr = instr;
		checked = false;
	} 
	
	public BCInstructionAlloc(BCInstruction instr, int iters) {
		this(instr);
		maxIter = iters;
		// TODO Auto-generated constructor stub
	}
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, bcclass.attributes.ExsuresTable)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public void setChecked() {
		checked = true;
	}
	
	public boolean isChecked( ) {
		return checked;
	} 

	/**
	 * @return the number of maximal iterations
	 */
	public int getMaxIterations() {
		return maxIter;
	}
	public BCInstruction getInstruction() { 
		return bcInstr;
	}
	
	public static int getLastLoopInstruction(BCLoopStart start) throws MalformedException {
		Vector loopEndPos = start.getLoopEndPositions();
		if ( loopEndPos == null) {
			throw new MalformedException(" the loop start doesnot have a loop end " + start.getBCIndex());
		}
		int max = 0;
		for ( int i = 0; i < loopEndPos.size() ; i++) {
			int ind =  ((Integer)loopEndPos.elementAt(i)).intValue();
			if (max  < ind ) {
					max = ind;
			}
		}
		return max;
	}
	
	
	int getAllocated() {
		if ( bcInstr instanceof BCLoopStart ) {
			BCInstruction instr = ((BCLoopStart)bcInstr).getWrappedInstruction();
			if ( instr instanceof BCNEW ) {
				return 1;
			} 
			return 0;
		}
		if ( bcInstr instanceof BCLoopEnd) {
			BCInstruction instr = ((BCLoopEnd)bcInstr).getWrappedInstruction();
			if ( instr instanceof BCNEW ) {
				return 1;
			}
			return 0;
			
		}
		if (bcInstr instanceof BCNEW) {
			return 1;
		}
		return 0;
	}
	/**
	 * @return Returns the loopConsumption.
	 */
	public int getLoopConsumption() {
		return loopConsumption*maxIter;
	}
	/**
	 * @param loopConsumption The loopConsumption to set.
	 */
	public void setLoopConsumptionPerIteration(int loopConsumption) {
		this.loopConsumption = loopConsumption;
	}
	
	/**
	 * initializes the specification for a loop - 
	 * the invariant: MemUsed <= MemUsed_before
	 * the modifies set,
	 * the decreases expression guaranteeing termination 
	 *
	 */
	public void initLoopSpec() {
		if (bcInstr instanceof BCLoopStart ) {
			BCLoopStart loopStart = (BCLoopStart)bcInstr;
			
			// construct the INVARIANT
			FieldAccess memUsed =  new FieldAccess(MemUsedConstant.MemUsedCONSTANT);
			
			// construct the expresssion upto iteration and before consumption
			Expression memUsedBefore = new OLD_LOOP( memUsed.copy(), loopStart.getPosition());
			Expression upToIteration = ArithmeticExpression.getArithmeticExpression(variant, new NumberLiteral(loopConsumption), ExpressionConstants.MULT);
			Expression upToIterationAndBefore = ArithmeticExpression.getArithmeticExpression( memUsedBefore, upToIteration , ExpressionConstants.ADD);
			
			
			Formula memAtEveryIterNotExceedsUpperBound =  
					new Predicate2Ar(memUsed, upToIterationAndBefore , PredicateSymbol.LESSEQ);
					
			Formula iterationBoundedByMaxIter = new Predicate2Ar( variant, new NumberLiteral( maxIter) , PredicateSymbol.LESSEQ);
			Formula invariant = Formula.getFormula( memAtEveryIterNotExceedsUpperBound , iterationBoundedByMaxIter, Connector.AND);
			loopStart.setInvariant(invariant);
			
			// construct the modifies set
			// we consider that the loop modifies the MemUsed field and the variant
			BCClass cl = loopStart.getMethod().getClazz();
			ModifiesExpression modExpr1 = null;
			if ( variant instanceof BCLocalVariable) {
				modExpr1 = new ModifiesLocalVariable((BCLocalVariable)variant,  cl);
			} 
			ModifiesExpression modExpr2 = new ModifiesIdent(new FieldAccess(MemUsedConstant.MemUsedCONSTANT ), cl );
			ModifiesSet modifSet = new ModifiesSet(new ModifiesExpression[]{modExpr1, modExpr2} , cl);
			
			loopStart.setModifies(modifSet);
			loopStart.setDecreases(decreases);
		}
	
	}
	
	
	
}
