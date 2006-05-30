/*
 * Created on Sep 22, 2004
 *
 * 
 */
package bytecode_wp.bcexpression;

import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.formula.Quantificator;
import bytecode_wp.utils.FreshIntGenerator;


/**
 * @author mpavlova
 *
 * this class is used to "freeze" local variables or 
 * class / instance fields at certain program state 
 */
public class ValueAtState extends Expression {
	private int atInstruction;
	
	
	/** 
	 * this class represents the value at a certain state of constant field references
	 * and local variables
	 * @param constant - the constant - field constant from constant pool or a local variable
	 * @param instrsNumber - the number of the instruction at which the value of the constant is instantiated
 	 */
	public ValueAtState(Expression constant, int instrNumber) {
		super(constant);
		atInstruction = instrNumber;
	}
	
	public Expression atState(int state) {
		return this;
	}
	
	/**
	 * this method freezes to the program point specifified by <code>instrIndex</code> only the
	 * expression expr
	 * @param instrIndex
	 * @param expr
	 * @return
	 */
	public Expression atState(int instrIndex, Expression expr) {
		return this;
	}
	
	/**
	 * returns the constant which is freezed by this instant
	 * @return
	 */
	public Expression getConstant() {
		return getSubExpressions()[0];
	}
	
	public Expression getType() {
		return getConstant().getType();
		/*if (getConstant() instanceof BCConstantFieldRef ) {
			BCConstantFieldRef constField = ( BCConstantFieldRef ) getConstant();
			return (JavaType)constField.getType();
		}*/
	}
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		// TODO Auto-generated method stub
		return this;
	}

	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		Expression constant = getConstant();
		String s = "(" + constant + "_at_instruction_"  + atInstruction +")";
		return s;
	}


	public int getAtInstruction() {
		return atInstruction;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return this;
	}
	
	public Expression removeOLD(int instrIndex) {
		if (atInstruction == instrIndex) {
			return getSubExpressions()[0];
		}
		return this;
	}
	
	

	public boolean equals(Expression _expr){
		if (! (_expr instanceof ValueAtState)) {
			return false;
		}
		ValueAtState _eAtState = (ValueAtState)_expr;
		if ( _eAtState.getAtInstruction() != getAtInstruction() ) {
			return false;
		} 
		if ( getConstant().equals(_eAtState.getConstant()) ) {
			return true;
		} 
		return false;
		
	}
    public Formula generateBoolExpressionConditions( ) {
        Formula condition = Predicate0Ar.TRUE;
        Expression subExp = getSubExpressions()[0];
        condition = subExp.generateBoolExpressionConditions();
        condition = (Formula )condition.atState( atInstruction, subExp.copy());
        return condition ;    
    }

    public  boolean isBooleanType() {
    	if (getSubExpressions()[0].isBooleanType()  ) {
    		return true;
    	}
    	return false;
    }
    
}
