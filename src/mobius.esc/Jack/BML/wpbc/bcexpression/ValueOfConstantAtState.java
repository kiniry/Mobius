/*
 * Created on Sep 22, 2004
 *
 * 
 */
package bcexpression;

import bcexpression.javatype.JavaType;
import constants.BCConstantFieldRef;

/**
 * @author mpavlova
 *
 * this  is a constantpool or local  variables , i.e. it is used to substitute constants from the consant pool or localvariables for a method 
 */
public class ValueOfConstantAtState extends Expression {
	private int atInstruction;
	
	
	/** 
	 * this class represents the value at a certain state of constant field references
	 * and local variables
	 * @param constant - the constant - field constant from constant pool or a local variable
	 * @param instrsNumber - the number of the instruction at which the value of the constant is instantiated
 	 */
	public ValueOfConstantAtState(Expression constant, int instrNumber) {
		super(constant);
		atInstruction = instrNumber;
	}
	
	public Expression atState(int state) {
		return this;
	}
	
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
	
	public Expression removeAtState(int instrIndex) {
		if (atInstruction == instrIndex) {
			return getSubExpressions()[0];
		}
		return this;
	}
	
}
