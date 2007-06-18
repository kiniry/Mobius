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
 * instruction and contains related BCEL structures.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class InstructionLineController extends BytecodeLineController {

  /**
   * The list of instructions in the method in which the current instruction
   * occurs.
   */
  protected InstructionList il;

  /**
   * A BCEL handle to the current instruction representation in BCEL
   * format.
   */
  protected InstructionHandle ih;

  /**
   * A BCEL object that represents the method in which the current instruction
   * is located.
   */
  protected MethodGen mg;

  /**
   * The mnemonic name of the current instruction.
   */
  protected String name;

  /**
   * The constructon creates the controler which
   * binds the instruction mnemonic with the line
   * number of the instruction.
   *
   * @param l the string representation of the line number
   * @param n the mnemonic name of the instruction
   */
  public InstructionLineController(final String l, final String n) {
    super(l);
    name = n;
    // tu moze w podklasach gdzie w podklasach instrukcje sie tworzy odpowiednio
  }

  /**
   * The method adds the link between the Umbra representation of
   * instructions to their representation in BCEL.
   *
   * @param ih the BCEL instruction handle that corresponds to the
   *       instruction associated with the current object
   * @param il the list of instructions in the current method
   * @param mg the object which represents the method of the current
   *    instruction in the BCEL representation of the current class
   *    in the bytecode editor
   * @param i method number in the current class
   * @return always true as the subclasses of the current class correspond to
   *     instructions
   */
  public final boolean addHandle(final InstructionHandle ih,
               final InstructionList il,
               final MethodGen mg, final int i) {
    System.out.println("InstructionLineController#addHandle name="+name);
    System.out.println("il="+il.toString());
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
   * @param nextLine    next line necessary to get handle -
   *     a new handle is inserted before the next one
   * @param cg      class generator from BCEL
   * @param ins      BCEL instruction (to generate handle)
   * @param metEnd    true if the line is inserted after the
   *     end of the method - then the 'nextLine' is actually the previous
   *     one and the handle is generated with 'append'
   * @param instructions  an array from BytecodeController that the new line
   *     is added
   * @param off      an offset in this array
   */
  public final void initHandle(final BytecodeLineController nextLine,
               final ClassGen cg, final Instruction ins,
               final boolean metEnd, final LinkedList instructions, final int off) {
//    controlPrint(nextLine);
    final InstructionHandle next = nextLine.getHandle();
    if (next != null) {
      final InstructionList newList = nextLine.getList();
      final MethodGen mg = nextLine.getMethod();
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
          else
            System.out.println(((BranchInstruction)ins).
                       getTarget().getPosition());
          ih = newList.insert(next, (BranchInstruction) ins);
        } else
          ih = newList.insert(next, ins);
      }
      il = newList;
      this.mg = mg;
      updateMethod(cg);
      if (ins != null) instructions.add(off + 1, this);
    }
  }

  /**
   * The debugging method that prints out to the standard output the
   * information on the line given in the parameter. It prints out:
   * + the name of the instruction,
   * + the position of the instruction handle
   *
   *  @param line the line for which the information is printed out
   */
  public static void controlPrint(final BytecodeLineController line) {
    System.out.println("Init: next line");
    if (line == null)
      System.out.println("Null");
    else {
      final Instruction ins = line.getInstruction();
      if (ins == null)
        System.out.println("Null instruction");
      else
        System.out.println(ins.getName());
      final InstructionHandle nih = line.getHandle();
      if (nih == null)
        System.out.println("Null handle");
      else
        System.out.println(nih.getPosition());
    }
  }

  /**
   * This is a debugging helper method which prints out to the standard
   * output the contents of the given BCEL instruction list.
   *
   * @param the isntruction list to print out
   */
  public static void printInstructionList(final InstructionList il) {
    InstructionHandle ih = il.getStart();
    if (ih==null) {
      System.out.println("start ih==null");
      return;
    }
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
   * @param oldLine    the previous structure
   * @param nextLine    next line, necessary if new handle must be generated
   * @param cg      class generator from BCEL
   * @param ins      BCEL instruction (to generate handle)
   * @param metEnd    true if the line is the last one of the method
   * @param instructions  an array from BytecodeController that the line
   *     is included
   * @param off      an offset in this array
   */
  public final void update(final BytecodeLineController oldLine,
      final BytecodeLineController nextLine, final ClassGen cg,
      final Instruction ins, final boolean metEnd, final boolean theLast,
      final LinkedList instructions, final int off) {
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
   * @param cg      class generator from BCEL
   */
  private void updateMethod(final ClassGen cg) {
    final Method oldMet = cg.getMethodAt(index);
    cg.replaceMethod(oldMet, mg.getMethod());
    //System.out.println(cg.getMethodAt(index).getCode().toString());
  }

  /**
   * @return the BCEL handle to the current instruction.
   */
  public final InstructionHandle getHandle() {
    return ih;
  }

  /**
   * @return the BCEL list of the instructions in the method that contains
   * the current instruction.
   */
  public final InstructionList getList() {
    return il;
  }

  /**
   * @return the method in which the current instruction is located
   */
  public final MethodGen getMethod() {
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
   * This method removes the current instruction line from BCEL structures
   *
   * @param nextLine a line after the removed one; it becomes a target of
   *         any jump instruction directed to the removed one
   * @param cg class generator from BCEL, this should be the same as in the
   *       {@ref BytecodeDocument} object for the currently edited
   *       bytecode file
   * @param instructions an array from {@ref BytecodeController} that
   *           contains the current line
   * @param off an offset in the <code>instructions</code> array which
   *      points to the instruction to be removed
   */
  public final void dispose(final BytecodeLineController nextLine,
            final ClassGen cg,
            final boolean theLast,
            final LinkedList instructions,
            final int off)
  {
    final InstructionHandle me = getHandle();
    final InstructionHandle next = nextLine.getHandle();
    System.out.println("InstructionLineController#dispose   name="+name);
    final InstructionTargeter[] tgters = ih.getTargeters();
    if (tgters!=null)
      for (int i=0; i<tgters.length; i++) {
        tgters[i].updateTarget(me, next);
      }
    try {
      il.delete(ih);
    } catch (TargetLostException e) {}
    ih = null;
    mg.setInstructionList(il);
    updateMethod(cg);
    System.out.println("I am here");
    instructions.remove(off);
    printInstructionList(il);
    System.out.println("Done");
  }

  /**
   * A list of characters that should be left intact by the method
   * {@ref #typ(String)}.
   */
  private static final String sp = ":-#%()<>;|";

  /**
   * The length of the {@ref sp} constant.
   */
  private static final int howManySp = sp.length();

  /**
   * Replaces some words in a string with single characters.
   * Each of the letters in the returned word means that in original line
   * there was the same character (if it belongs to string {@link #sp sp}) or
   * a corresponding word listed below (otherwise):
   * <ul>
   * <li> C means a string within double quotes
   * <li> W means one or more following whitespaces
   * <li> D means a natural number
   * <li> X means any other word
   * </ul>
   * @param line  processing string
   * @return    line with each (maximal) word from list above
   * (excluding characters from sp) replaced with corresponding character
   */
  private static String typ(String line) {
    String s = "";
    boolean b;
    line = line + "|";
    for (int i = 0; i < line.length();) {
      b = false;
      for (int j = 0; j < howManySp; j++)
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
        while ((line.charAt(i) != '"') ||
               (line.charAt(i - 1) == '\\')) {
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
   * @param lt  comparing string
   * @param typ  class of acceptable strings
   * @return    <code> true </code> if lt is one of strings from typ
   *         <code> false </code> otherwise
   */
  private static boolean compare(final String lt, final String typ) {
    if (lt.equals(typ))
      return true;
    if ((lt.length() == 0) || (typ.length() == 0))
      return false;
    if (typ.startsWith("?{")) {
      final int n = typ.indexOf("}");
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
   * @param line  the line of bytecode (with removed all comments)
   * @param typ  the pattern
   * @return    <code> true </code> if line matches pattern
   *         <code> false </code> otherwise
   */
  public final boolean chkcorr(final String line, final String typ) {
    final boolean b = compare(typ(line), "?D:?WX" + typ + "|");
    return b;
  }
}
