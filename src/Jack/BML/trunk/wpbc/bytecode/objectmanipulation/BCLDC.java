/*
 * Created on Apr 6, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.objectmanipulation;

import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.InstructionHandle;

import constants.BCCONSTANT_LITERAL;

import bcclass.BCConstantPool;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCInstruction;

import formula.Formula;

/**
 * @author mpavlova
 *
 *  Push item from constant pool - LDC , LDC_W
 * 
 *  Format ldc index
 * 
 *  Operand Stack : ... ==> ..., value
 * 
 * Description: The index is an unsigned byte that must be a valid index into the runtime constant 
 * pool of the current class.
 * The runtime constant pool entry at index either must be a runtime constant of type int or 
 * float, or must be a symbolic reference to a string literal.
 * If the runtime constant pool entry is a runtime constant of type int or float, 
 * the numeric value of that runtime constant is pushed onto the operad 
 * stack as an int or float, respectively.
 *
 * Otherwise, the runtime constant pool entry must be a reference to an instance of class 
 * String representing a string literal.
 * A reference to that instance, value, is pushed onto the operand stack.
 * 
 * 
 * Notes
 *
 *   The ldc instruction can only be used to push a value of type float taken from the 
 *   float value set because a constant of type float in the constant pool 
 *    must be taken from the float value set.
 * psi^n[ t <-- t+1] [S(t+1) <-- cp_at(index)]
 */

//change - before the superclass BCExceptionThrower.java
public class BCLDC extends BCInstruction implements BCCPInstruction {
	private int cpIndex;
	private JavaType type;
	
	
	private BCConstantPool cp;
	/**
	 * @param _instruction
	 */
	public BCLDC(InstructionHandle _instruction, JavaType _type , BCConstantPool _cp) {
		super(_instruction);
		setIndex( ( (CPInstruction)_instruction.getInstruction()).getIndex());
	    setType(_type);
	    cp = _cp;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#setIndex(int)
	 */
	public void setIndex(int _index) {
		cpIndex = _index;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCIndexedInstruction#getIndex()
	 */
	public int getIndex() {
		return cpIndex;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
		type =_type;
	}

	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		Stack top_stack_plus_1 = new Stack(Expression.getCOUNTER_PLUS_1());
		wp = (Formula)wp.substitute(top_stack_plus_1, ((BCCONSTANT_LITERAL) getConstantPool().getConstant(getIndex())).getLiteral());
		return wp;
	}

	/**
	 * @return
	 */
	public BCConstantPool getConstantPool() {
		return cp;
	}

}
