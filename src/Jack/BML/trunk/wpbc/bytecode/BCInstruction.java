/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;


import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;

import bcexpression.javatype.JavaType;
import formula.Formula;





/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract  class BCInstruction  implements ByteCode{

	private Formula wp;
	
	/**
	 * this field should disappear in the end. Only the needed information extracted from the object should reamain.
	 */
	private InstructionHandle instructionHandle;	
	
	/**
	 * the preceding instruction in the bytecode
	 */
	private BCInstruction prev;
	
	/**
	 * the next instruction in the bytecode
	 */	
	private BCInstruction next;
	
	/**
	 * a list of instructions that target to this one 
	 */
	private Vector targeters;
	
	//the index at which this instruction  is in the bytecode
	private int position;
	private int bcIndex;
	private int offset;	
	private byte instructionCode;

	
	/**
	 * exceptions that this throw instruction may cause
	 */
	private JavaType[] exceptions;
	
	public BCInstruction(InstructionHandle  _instruction)  {
		instructionHandle = _instruction; 
		setPosition(instructionHandle);
	}
	
	public InstructionHandle getInstructionHandle() {
		return instructionHandle;
	}
	
	public void setNext(BCInstruction _next)  {
		next = _next;
	}
	
	public void setPrev(BCInstruction _prev )  {
		prev = _prev;
	}
	
	public BCInstruction getNext() {
		return next;
	}
	
	public BCInstruction getPrev() {
		return prev;
	}

	/**
	 * @param i - this the index at which 
	 * this command appears in the bytecode array of instruction 
	 */
	public void setBCIndex(int i) {
		bcIndex = i;
	}
	
	/**
	 *  @return
	 *  the index at which 
	 *  this command appears in the bytecode array of instruction 
	 */
	public int getBCIndex() {
		return bcIndex;
	}
	
	/*
	 * @return - the offset of the instruction 
	 * from the beginning 
	 */
	public int getPosition() {
		return position;
	}
	
	private void setPosition(InstructionHandle instructionHandle) {
		position = instructionHandle.getPosition();
	}
	/**
	 * @return
	 */
	public Vector getTargeters() {
		return targeters;
	}

	/**
	 * @param vector
	 */
	public void setTargeters(Vector vector) {
		targeters = vector;
	}
	
	/**
	 * adds an instruction that is targets to this one
	 * @param _t
	 */
	public void addTargeter(BCInstruction _t){
		if  (targeters == null) {
			targeters = new Vector();
		}
		targeters.add(_t);
	} 
	
	/**
	 * sets the postcondition 
	 */
	private void wpTargeters() {
		
		
	}
	
	public void dump(String _s) {
		
		if (true ) {
			System.out.println(_s);
		}
	}

	/**
	 * @return
	 */
	public byte getInstructionCode() {
		return instructionCode;
	}

	/**
	 * @param b
	 */
	public void setInstructionCode(byte b) {
		instructionCode = b;
	}

}
