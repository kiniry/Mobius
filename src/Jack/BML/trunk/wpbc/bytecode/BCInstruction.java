/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;


import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;

import utils.Util;

import bcexpression.javatype.JavaType;
import formula.Formula;





/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract  class BCInstruction  implements ByteCode{


	
	/**
	 * this field should disappear in the end. Only the needed information extracted from the object should reamain.
	 */
	public InstructionHandle instructionHandle;	
	
	/**
	 * the preceding instruction in the bytecode
	 */
	private int prev = -1;
	
	/**
	 * the next instruction in the bytecode
	 */	
	private int next = -1;
	
	/**
	 * a list of instructions that target to this one 
	 */
	private Vector targeters;
	
	
	
	//the index at which this instruction  is in the bytecode
	private int position;
	
	private BCInstruction[] bytecode;
	
	/**
	 * the index in the bytecode array at which this instruction appears
	 */
	private int bcIndex;
	private int offset;	
	private byte instructionCode;


	private Formula assertion;
	
	/**
	 * exceptions that this throw instruction may cause
	 */
	private JavaType[] exceptions;
	
	public BCInstruction() {
	}
	
	public BCInstruction(InstructionHandle  _instruction)  {
		instructionHandle = _instruction; 
		setPosition(instructionHandle.getPosition());
	}
	
	public InstructionHandle getInstructionHandle() {
		return instructionHandle;
	}
	
	public void setNext(BCInstruction _next)  {
		if ( _next == null) {
			next = -1;
			return; 
		}
		next = _next.getPosition();
	}
	
	public void setPrev(BCInstruction _prev )  {
		if ( _prev == null) {
			prev = -1;
			return;
		}
		prev = _prev.getPosition();
	}
	
	public BCInstruction getNext() {
		if (next == -1) {
			return null;
		}
		BCInstruction instrNext = Util.getBCInstructionAtPosition( bytecode, next);
		return instrNext;
	}
	
	public BCInstruction getPrev() {
		if (prev == -1) {
			return null;
		}
		BCInstruction instrPrev = Util.getBCInstructionAtPosition( bytecode, prev);
		return instrPrev;
	}

	/**
	 * @param i - the index at which 
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
	
	public void setPosition(int  _position) {
		position = _position;
	}
	/**
	 * @return
	 */
	public Vector getTargeters() {
		if (targeters == null) {
			return null;
		}
		Vector targetersInstr = new Vector();
		
		for (int i = 0; i < targeters.size(); i++) {
			int pos = ( (Integer)targeters.elementAt(i)).intValue();
			if (pos  == -1 ) {
				continue;
			}
			BCInstruction instr = Util.getBCInstructionAtPosition( bytecode, pos );
			targetersInstr.add(instr);
		}
		return targetersInstr;
	}

	/**
	 * @param vector
	 * the vector should contain objects of type BCInstruction
	 */
	public void setTargeters(Vector vector) {
		if (vector == null) {
			return;
		}
		targeters = new Vector();
		for (int i = 0; i < vector.size() ; i++) {
			BCInstruction instr = (BCInstruction)vector.elementAt(i);
			targeters.add(new Integer( instr.getPosition()));
		}
	}
	
	/**
	 * adds an instruction that is targets to this one
	 * @param _t
	 */
	public void addTargeter(BCInstruction _t){
		if  (targeters == null) {
			targeters = new Vector();
		}
		targeters.add(new Integer( _t.getPosition()));
	} 
	
	
	
	/**
	 * removes a targeter instruction from the vector of targeters instructions. Used when identifying loops
	 * @param instr
	 */
	public void removeTargeter(BCInstruction instr) {
		if (targeters == null) {
			return;
		}
		targeters.remove(new Integer( instr.getPosition() ));
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

	/**
	 * @return Formula - if there is an assertion specified,
	 * otherwise returns null
	 */
	public Formula getAssert() {
		return assertion;
	}

	/**
	 * Sets the invariant if there is one specified
	 * @param invariant The invariant to set
	 */
	public void setAssert(Formula assertion) {
		this.assertion = assertion;
	}

	public String toString() {
		return ""+  getPosition() + " :  "+ getInstructionHandle().getInstruction() ;
	}

	/**
	 * @return Returns the bytecode.
	 */
	public void setBytecode(BCInstruction[]  b) {
		 bytecode = b;
	}
	/**
	 * @return Returns the bytecode.
	 */
	public BCInstruction[] getBytecode() {
		return bytecode;
	}
}
