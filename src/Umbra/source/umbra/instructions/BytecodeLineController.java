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
	
	public boolean correct()	{
		return false;
	}
	
	public void dispose(BytecodeLineController nextLine, ClassGen cg, boolean theLast, LinkedList instructions, int off) {
		
	}

	public void setIndex(int index2) {
		this.index = index2;		
	}

}
