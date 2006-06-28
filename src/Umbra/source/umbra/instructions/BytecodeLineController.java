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

	protected String line;
	protected int index;

	public BytecodeLineController(String l) {
		super();
		line = l;
	}
	
	public boolean addHandle(InstructionHandle ih, InstructionList il, MethodGen mg, int i) {
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
	
	public void setTarget(InstructionList il, Instruction ins) {
		
	}
	
	public void initHandle(BytecodeLineController nextLine, ClassGen cg, Instruction ins, boolean metEnd, LinkedList instructions, int off) {	
	}
	
	public void update(BytecodeLineController oldLine, BytecodeLineController nextLine, ClassGen cg, Instruction ins, boolean metEnd, boolean theLast, LinkedList instructions, int off) {
		if (oldLine.getHandle() != null) {
			oldLine.dispose(nextLine, cg, theLast, instructions, off);
		}
	}
	
	public InstructionHandle getHandle() {
		return null;
	}
	
	public InstructionList getList() {
		return null;
	}
	
	public MethodGen getMethod() {
		return null;
	}
	
	public int getIndex() {
		return index;
	}
	
	//&*zmiana nazwy! usuwam z podklas!
	protected String extractPoint(String l) {
		String s;
		s = "";
		int ii = 0;
		int jj = l.length();
		for (ii = 0; ii < jj; ii++)
			if (!(Character.isWhitespace(l.charAt(ii)))) {
				s += l.charAt(ii);
			}
		return s;	
	}
	
	/**
	 * This method is used to check some basic condition of 
	 * correctness. For non-instruction line this is the only 
	 * checking. If it returns true the line is regarded 
	 * to be correct.
	 * 
	 * @return	true if the instruction is correct
	 * @see		InstructionLineController#correct()
	 */
	public boolean correct()	{
		return false;
	}
	
	public void dispose(BytecodeLineController nextLine, ClassGen cg, boolean theLast, LinkedList instructions, int off) {
		
	}

	public void setIndex(int index2) {
		this.index = index2;		
	}

}
