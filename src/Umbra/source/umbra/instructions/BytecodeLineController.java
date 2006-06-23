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
     * TODO write description
     */    
    protected String line;
    /**
     * TODO write description
     */    
    protected int index;

    /**
     * TODO write description
     * 
     * @param l TODO write description
     */    
    public BytecodeLineController(String l) {
		super();
		line = l;
	}
	
    /**
     * TODO write description
     * 
     * @param ih TODO write description
     * @param il TODO write description
     * @param mg TODO write description
     * @param i TODO write description
     * @return TODO write description
     */    
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
	
    /**
     * TODO write description
     * 
     * @param il TODO write description
     * @param ins TODO write description
     */    
    public void setTarget(InstructionList il, Instruction ins) {
		
	}
	
    /**
     * TODO write description
     * 
     * @param nextLine TODO write description
     * @param cg TODO write description
     * @param ins TODO write description
     * @param metEnd TODO write description
     * @param instructions TODO write description
     * @param off TODO write description
     */    
    public void initHandle(BytecodeLineController nextLine, ClassGen cg, Instruction ins, boolean metEnd, LinkedList instructions, int off) {	
	}
	
    /**
     * TODO write description
     * 
     * @param oldLine TODO write description
     * @param nextLine TODO write description
     * @param cg TODO write description
     * @param ins TODO write description
     * @param metEnd TODO write description
     * @param theLast TODO write description
     * @param instructions TODO write description
     * @param off TODO write description
     */    
    public void update(BytecodeLineController oldLine, BytecodeLineController nextLine, ClassGen cg, Instruction ins, boolean metEnd, boolean theLast, LinkedList instructions, int off) {
		if (oldLine.getHandle() != null) {
			oldLine.dispose(nextLine, cg, theLast, instructions, off);
		}
	}
	
    /**
     * TODO write description
     * 
     * @return TODO write description
     */    
    public InstructionHandle getHandle() {
		return null;
	}
	
    /**
     * TODO write description
     * 
     * @return TODO write description
     */    
    public InstructionList getList() {
		return null;
	}
	
    /**
     * TODO write description
     * 
     * @return TODO write description
     */    
    public MethodGen getMethod() {
		return null;
	}
	
    /**
     * TODO write description
     * 
     * @return TODO write description
     */    
    public int getIndex() {
		return index;
	}
	
	//&*zmiana nazwy! usuwam z podklas!
    /**
     * TODO write description
     * 
     * @param l TODO write description
     */    
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
	
    /**
     * TODO write description
     * 
     * @param nextLine TODO write description
     * @param cg TODO write description
     * @param theLast TODO write description
     * @param instructions TODO write description
     * @param off TODO write description
     */    
    public void dispose(BytecodeLineController nextLine, ClassGen cg, boolean theLast, LinkedList instructions, int off) {
		
	}

    /**
     * TODO write description
     * 
     * @param index2 TODO write description
     */    
    public void setIndex(int index2) {
		this.index = index2;		
	}

}
