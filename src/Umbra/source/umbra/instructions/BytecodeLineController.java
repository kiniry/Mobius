/*
 * Created on 2005-05-17
 */
package umbra.instructions;
import java.util.LinkedList;

import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

/**
 * This is completely abstract class that contains some information
 * useful when the line is modified or BCEL structure is created.
 * Most details are implemented in subclasses.
 * 
 * @author Tomek Batkiewicz
 */
public abstract class BytecodeLineController {

	/**
	 * The string representation of the bytecode line number.
	 */
	protected String line;
	
	/**
	 * TODO
	 */
	protected int index;

	/**
	 * TODO
	 * 
	 * @param l the string representation of the line number.
	 */
	public BytecodeLineController(String l) {
		super();
		line = l;
	}
	
	/**
	 * TODO
	 */
	public boolean addHandle(InstructionHandle ih, 
			                 InstructionList il, 
			                 MethodGen mg, 
			                 int i) {
		index = i;
		return false;
	}
	
	/**
	 * This method is redefined in each subclass of particular
	 * instruction type. It is used for creating a handle
	 * containing appropriate BCEL instruction object
	 * that matches with the instruction name.
	 * 
	 * @return Handle to the appropriate instruction;
	 * 	null if the line is not an instruction one.
	 */
	public Instruction getInstruction() {
		return null;
	}
	
	/**
	 * TODO
	 */
	public void setTarget(InstructionList il, Instruction ins) {
		
	}
	
	/**
	 * TODO
	 */
	public void initHandle(BytecodeLineController nextLine, ClassGen cg, Instruction ins, boolean metEnd, LinkedList instructions, int off) {	
	}
	
	/**
	 * TODO
	 */
	public void update(BytecodeLineController oldLine, 
			           BytecodeLineController nextLine, 
			           ClassGen cg, 
			           Instruction ins, 
			           boolean metEnd, boolean theLast, 
			           LinkedList instructions, int off) {
		if (oldLine.getHandle() != null) {
			oldLine.dispose(nextLine, cg, theLast, instructions, off);
		}
	}
	
	/**
	 * TODO
	 */
	public InstructionHandle getHandle() {
		return null;
	}
	
	/**
	 * TODO
	 */
	public InstructionList getList() {
		return null;
	}
	
	/**
	 * TODO
	 */
	public MethodGen getMethod() {
		return null;
	}
	
	/**
	 * TODO
	 */
	public int getIndex() {
		return index;
	}
	

	
	/**
	 * This method is used to check some basic condition of 
	 * correctness. For non-instruction line this is the only 
	 * checking. It is usually redefined in the subclasses so that 
	 * if it returns true the line is regarded to be correct.
	 * 
	 * @return	true if the instruction is correct
	 * @see		InstructionLineController#correct()
	 */
	public boolean correct()	{
		return false;
	}
	
	/**
	 * TODO
	 */
	public void dispose(BytecodeLineController nextLine, 
			            ClassGen cg, 
			            boolean theLast, 
			            LinkedList instructions, int off) {
		
	}

	/**
	 * TODO
	 */
	public void setIndex(int index2) {
		this.index = index2;		
	}
	
	/**
	 * The method returns the String representation of the current instruction
	 * content.
	 * 
	 * @return the representation of the line
	 */
	public String getLineContent() {
		return line;
	}
}
