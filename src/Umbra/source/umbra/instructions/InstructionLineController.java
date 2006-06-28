/*
 * Created on 2005-05-17
 */
package umbra.instructions;

import java.util.LinkedList;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InstructionTargeter;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.TargetLostException;


/**
 * This class defines a structure that describes a single Bytecode
 * instruction and contains related BCEL structures
 * 
 * @author Wojciech W¹s, Tomek Batkiewicz
 */
public abstract class InstructionLineController extends BytecodeLineController {

	protected InstructionList il;
	protected InstructionHandle ih;
	protected MethodGen mg;
	protected String name; 
	
	public InstructionLineController(String l, String n) {
		super(l);
		name = n;
		// tu moze w podklasach gdzie w podklasach instrukcje sie tworzy odpowiednio
	}
	
	public boolean addHandle(InstructionHandle ih, InstructionList il, MethodGen mg, int i) {
		this.ih = ih;
		this.il = il;
		this.mg = mg;
		index = i;
		return true;
	}
	
	/**
	 * This method is executed when a new line is inserted to
	 * the method and it must be added to BCEL structures,
	 * especially new handle is generated 
	 * 
	 * @param nextLine		next line necessary to get handle -
	 * 		a new handle is inserted before the next one 
	 * @param cg			class generator from BCEL 
	 * @param ins			BCEL instruction (to generate handle)
	 * @param metEnd		true if the line is inserted after the
	 * 		end of the method - then the 'nextLine' is actually the previous
	 * 		one and the handle is generated with 'append' 
	 * @param instructions	an array from BytecodeController that the new line
	 * 		is added
	 * @param off			an offset in this array
	 */
	public void initHandle(BytecodeLineController nextLine, ClassGen cg, Instruction ins, boolean metEnd, LinkedList instructions, int off) {
//		controlPrint(nextLine);
		InstructionHandle next = nextLine.getHandle();
		if (next != null) {
			InstructionList newList = nextLine.getList();
			MethodGen mg = nextLine.getMethod();
			//index = nextLine.getIndex();
			if (ins == null) {
				ih = null;
			}
			else if (metEnd) {
				ih = newList.append(ins);
			}
			else {
				if (ins instanceof BranchInstruction){
					if (((BranchInstruction)ins).getTarget() == null)
						System.out.println("null target");
					else System.out.println(((BranchInstruction)ins).getTarget().getPosition());
					ih = newList.insert(next, (BranchInstruction) ins);
				}
				else ih = newList.insert(next, ins);
			}
			il = newList;
			this.mg = mg;
			updateMethod(cg);
			if (ins != null) instructions.add(off + 1, this);
		}
	}
	
	private void controlPrint(BytecodeLineController line) {
		System.out.println("Init: next line");
		if (line == null) System.out.println("Null");
		else {
			Instruction ins = line.getInstruction();
			if (ins == null) System.out.println("Null instruction");
			else System.out.println(ins.getName());
			InstructionHandle nih = line.getHandle();
			if (nih == null) System.out.println("Null handle");
			else System.out.println(nih.getPosition());
		}
	}
	
	private void printInstructionList(InstructionList il) {
		InstructionHandle ih = il.getStart();
		System.out.println(ih.getInstruction().getName());
		do {
			ih = ih.getNext();
			System.out.println(ih.getInstruction().getName());
		}
		while (ih != il.getEnd());
	}
	
	/**
	 * This method is executed when a line is modificated
	 * but not inserted or removed; it usually replaces BCEL
	 * instruction related to a handle, but it can also call
	 * dispose method (if new version is incorrect) or
	 * init handle (if the previous one was incorrect).  
	 * 
	 * @param oldLine		the previous structure
	 * @param nextLine		next line, necessary if new handle must be generated 
	 * @param cg			class generator from BCEL 
	 * @param ins			BCEL instruction (to generate handle)
	 * @param metEnd		true if the line is the last one of the method
	 * @param instructions	an array from BytecodeController that the line
	 * 		is included
	 * @param off			an offset in this array
	 */
	public void update(BytecodeLineController oldLine,
			BytecodeLineController nextLine, ClassGen cg,
			Instruction ins, boolean metEnd, boolean theLast,
			LinkedList instructions, int off) {
		System.out.println("oldline="+oldLine.line);
		System.out.println("nextline="+nextLine.line);
		System.out.println("cg="+((cg==null)?"null":"ok"));
		System.out.println("ins="+((ins==null)?"null":ins.getName()));
		System.out.println("MetEnd=" + metEnd);
		System.out.println("theLast=" + theLast);
		System.out.println("off=" + off);
		mg = oldLine.getMethod();
		il = oldLine.getList();
		ih = oldLine.getHandle();
		index = oldLine.getIndex();
		System.out.println("ih="+((ih==null)?"null":
			((ih.getInstruction()==null)?"null ins":ih.getInstruction().getName())));
		if (il == null) System.out.println("il = null");
		else printInstructionList(il);
		if (ih == null) {
			System.out.println("A");
			initHandle(nextLine, cg, ins, metEnd, instructions, off);
		}
		else if (ih.getInstruction() == null) {
			System.out.println("B");
			initHandle(nextLine, cg, ins, metEnd, instructions, off);
		}
		else if (ins != null) {
			System.out.println("C");
			ih.setInstruction(ins);
			System.out.println();
			updateMethod(cg);
			instructions.set(off, this);
		}
		else {
			System.out.println("D");
			dispose(nextLine, cg, theLast, instructions, off);
		}
	}
	
	/**
	 * Replacing BCEL method with the new one with updated
	 * instruction list
	 * 
	 * @param cg			class generator from BCEL 
	 */
	private void updateMethod(ClassGen cg) {
		Method oldMet = cg.getMethodAt(index);
		cg.replaceMethod(oldMet, mg.getMethod());
		//System.out.println(cg.getMethodAt(index).getCode().toString());
	}	
	
	public InstructionHandle getHandle() {
		return ih;
	}
	
	public InstructionList getList() {
		return il;
	}

	public MethodGen getMethod() {
		return mg;
	}
	
	/**
	 * This method is redefined in each subclass. It is used
	 * to check some basic condition of correctness. A positive
	 * result is necessary to continue any attempt of
	 * generating BCEL structures about the line.
	 * 
	 * @return true if the instruction is correct
	 */
	public boolean correct()
	{
		return true;
	}
	
	/**
	 * Removing line from BCEL structures
	 * 
	 * @param nextLine		a line after the removed one; it becomes
	 * 			a target of any jump instruction directed to the removed one 
	 * @param cg			class generator from BCEL 
	 * @param instructions	an array from BytecodeController that the line
	 * 		is included
	 * @param off			an offset in this array
	 */
	public void dispose(BytecodeLineController nextLine, ClassGen cg, boolean theLast, LinkedList instructions, int off)
	{
		InstructionHandle next = nextLine.getHandle();
		try {
			il.delete(ih);
		} catch (TargetLostException e) {
		    InstructionHandle[] targets = e.getTargets();
		    for(int i = 0; i < targets.length; i++) {
		      InstructionTargeter[] targeters = targets[i].getTargeters();
		      for(int j = 0; j < targeters.length; j++) {
		         targeters[j].updateTarget(targets[i], next);
		      }
		    }
		}
		ih = null;
		updateMethod(cg);
		System.out.println("I am here");
		instructions.remove(off);
		printInstructionList(il);
		System.out.println("Done");
	}

	// dodane 7.27.19
	final static String sp = ":-#%()<>;|";
	final static int ileSp = sp.length();
	
	/**
	 * Replaces some words in a string with single characters.
	 * Each of the letter in returned word means that in original line there was
	 * the same character (if it belongs to string {@link #sp sp}) or
	 * a corresponding word listed below (otherwise):
	 * <ul>
	 * <li> C means a string within double quotes
	 * <li> W means one or more following whitespaces
	 * <li> D means a natural number
	 * <li> X means any other word
	 * </ul>
	 * @param line	processing string
	 * @return		line with each (maximal) word from list above
	 * (excluding characters from sp) replaced with corresponding character 
	 */
	private static String typ(String line) {
		String s = "";
		char ch;
		boolean b;
		line = line + "|";
		for (int i = 0; i < line.length();) {
			b = false;
			for (int j = 0; j < ileSp; j++)
				if (sp.charAt(j) == line.charAt(i)) {
					s = s + line.charAt(i);
					i++;
					b = true;
				}
			if (b)
				continue;
			if (line.charAt(i) == '"') {
				s = s + "C";
				i++;
				while ((line.charAt(i) != '"')
					|| (line.charAt(i-1) == '\\')) {
						i++;
						if (i >= line.length() - 1)
							break;
				}
				i++;
				continue;
			}
			if (Character.isWhitespace(line.charAt(i))) {
				s = s + "W";
				while (Character.isWhitespace(line.charAt(i)))
					i++;
				continue;
			}
			if (Character.isDigit(line.charAt(i))) {
				s = s + "D";
				while (Character.isDigit(line.charAt(i)))
					i++;
				continue;
			}
			if (!s.endsWith("X")) {
				s = s + "X";
			}
			i++;
		}
		return s;
	}
	
	/**
	 * Compares a string and class of strings typ, represented also as string:
	 * a "?" character in typ means that the following character (or the following
	 * word within {} brackets) are optional, any other character must be the same
	 * as the corresponding character from corresponding string.
	 * For example, string "A?B?{CD}E" as a second argument (typ) represents
	 * the set of strings: {"AE", "ABE", "ACDE", "ABCDE"}.
	 * 
	 * @param lt	comparing string
	 * @param typ	class of acceptable strings
	 * @return		<code> true </code> if lt is one of strings from typ
	 * 				<code> false </code> otherwise
	 */
	private static boolean compare(String lt, String typ) {
		if (lt.equals(typ))
			return true;
		if ((lt.length() == 0) || (typ.length() == 0))
			return false;
		if (typ.startsWith("?{")) {
			int n = typ.indexOf("}");
			if (n > 2)
				if (compare(lt, typ.substring(n+1)))
					return true;
			return compare(lt, typ.substring(2, n) + typ.substring(n+1));
		}
		if (typ.startsWith("?"))
			return (compare(lt, typ.substring(1))
					|| ((typ.length() > 1)
							&& compare(lt, typ.substring(2))));
		if (lt.charAt(0) != typ.charAt(0))
			return false;
		return compare(lt.substring(1), typ.substring(1));
	}

	/**
	 * Compares line with a pattern.
	 * @param line	the line of bytecode (with removed all comments)
	 * @param typ	the pattern
	 * @return		<code> true </code> if line matches pattern
	 * 				<code> false </code> otherwise 
	 */
	public boolean chkcorr(String line, String typ) {
		boolean b = compare(typ(line), "?D:?WX" + typ + "|");
		return b;
	}
	// koniec
	
}
