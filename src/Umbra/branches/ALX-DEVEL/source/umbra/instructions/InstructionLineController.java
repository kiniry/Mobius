/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
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

import umbra.UmbraPlugin;

/**
 * This class defines a structure that describes a single bytecode
 * instruction and contains related BCEL structures.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class InstructionLineController extends BytecodeLineController {

  /**
   * TODO.
   */
  private static final int RBRACE_AFTER = 2;

  /**
   * A list of characters that should be left intact by the method
   * {@ref #typ(String)}.
   */
  private static final String SKIP_CHARS = ":-#%()<>;|";

  /**
   * The length of the {@ref SKIP_CHARS} constant.
   */
  private static final int SKIP_CHARS_LEN = SKIP_CHARS.length();

  /**
   * The list of instructions in the method in which the current instruction
   * occurs.
   */
  private InstructionList my_instr_list;

  /**
   * A BCEL handle to the current instruction representation in BCEL
   * format.
   */
  private InstructionHandle my_instr_handle;

  /**
   * A BCEL object that represents the method in which the current instruction
   * is located.
   */
  private MethodGen my_methodgen;

  /**
   * The mnemonic name of the current instruction.
   */
  private String my_name;

  /**
   * The constructon creates the controler which
   * binds the instruction mnemonic with the line text. The name is set locally
   * while the assignment of the line is done in the constructor of the
   * superclass.
   *
   * @param a_line_text the string representation of the line text
   * @param a_name the mnemonic name of the instruction
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public InstructionLineController(final String a_line_text,
                                   final String a_name) {
    super(a_line_text);
    setName(a_name);
  }

  /**
   * The method adds the link between the Umbra representation of
   * instructions to their representation in BCEL.
   *
   * @param a_handle the BCEL instruction handle that corresponds to the
   *       instruction associated with the current object
   * @param a_list the list of instructions in the current method
   * @param a_method_gen the object which represents the method of the current
   *    instruction in the BCEL representation of the current class
   *    in the bytecode editor
   * @param a_method_num method number in the current class
   * @return always true as the subclasses of the current class correspond to
   *     instructions
   */
  public final boolean addHandle(final InstructionHandle a_handle,
               final InstructionList a_list,
               final MethodGen a_method_gen, final int a_method_num) {
    UmbraPlugin.messagelog("InstructionLineController#addHandle my_name=" +
                           getName());
    UmbraPlugin.messagelog("my_instr_list=" + a_list.toString());
    this.my_instr_handle = a_handle;
    this.my_instr_list = a_list;
    this.my_methodgen = a_method_gen;
    setIndex(a_method_num);
    return true;
  }

  /**
   * This method is executed when a new line is inserted to
   * the method and it must be added to BCEL structures,
   * especially new handle is generated. TODO more details
   *
   * @param a_next_line a next line, necessary to get handle - a new handle is
   *   inserted before the next one
   * @param a_class_gen a class generator from BCEL
   * @param an_instruction a BCEL instruction (to generate handle)
   * @param a_method_end <code>true</code> if the line is inserted after the
   *   end of the method - then the <code>a_next_line</code> is actually the
   *   previous one and the handle is generated with 'append'
   * @param the_instructions an array from {@ref BytecodeController} that the
   *   new line is added to
   * @param an_offset an offset in this array
   */
  public final void initHandle(final BytecodeLineController a_next_line,
               final ClassGen a_class_gen, final Instruction an_instruction,
               final boolean a_method_end, final LinkedList the_instructions,
               final int an_offset) {
//    controlPrint(nextLine);
    final InstructionHandle next = a_next_line.getHandle();
    if (next != null) {
      final InstructionList newList = a_next_line.getList();
      final MethodGen a_mg = a_next_line.getMethod();
      //my_index = nextLine.getIndex();
      if (an_instruction == null) {
        my_instr_handle = null;
      } else if (a_method_end) {
        my_instr_handle = newList.append(an_instruction);
      } else {
        if (an_instruction instanceof BranchInstruction) {
          if (((BranchInstruction)an_instruction).getTarget() == null)
            UmbraPlugin.messagelog("null target");
          else
            UmbraPlugin.messagelog(
                       Integer.toString(((BranchInstruction)an_instruction).
                       getTarget().getPosition()));
          my_instr_handle = newList.insert(next,
                                           (BranchInstruction)an_instruction);
        } else
          my_instr_handle = newList.insert(next, an_instruction);
      }
      my_instr_list = newList;
      this.my_methodgen = a_mg;
      updateMethod(a_class_gen);
      if (an_instruction != null) the_instructions.add(an_offset + 1, this);
    }
  }

  /**
   * The debugging method that prints out to the standard output the
   * information on the line given in the parameter. It prints out:
   * <ul>
   *   <li> the name of the instruction,</li>
   *   <li> the position of the instruction handle</li>
   * </ul>
   *
   *  @param a_line the line for which the information is printed out
   */
  public static void controlPrint(final BytecodeLineController a_line) {
    UmbraPlugin.messagelog("Init: next line");
    if (a_line == null)
      UmbraPlugin.messagelog("Null");
    else {
      final Instruction ins = a_line.getInstruction();
      if (ins == null)
        UmbraPlugin.messagelog("Null instruction");
      else
        UmbraPlugin.messagelog(ins.getName());
      final InstructionHandle nih = a_line.getHandle();
      if (nih == null)
        UmbraPlugin.messagelog("Null handle");
      else
        UmbraPlugin.messagelog(Integer.toString(nih.getPosition()));
    }
  }

  /**
   * This is a debugging helper method which prints out to the standard
   * output the contents of the given BCEL instruction list.
   *
   * @param an_ilist the isntruction list to print out
   */
  public static void printInstructionList(final InstructionList an_ilist) {
    InstructionHandle ih = an_ilist.getStart();
    if (ih == null) {
      UmbraPlugin.messagelog("start my_instr_handle==null");
      return;
    }
    UmbraPlugin.messagelog(ih.getInstruction().getName());
    do {
      ih = ih.getNext();
      UmbraPlugin.messagelog(ih.getInstruction().getName());
    }
    while (ih != an_ilist.getEnd());
  }

  /**
   * This method is executed when a line is modificated
   * but not inserted or removed; it usually replaces BCEL
   * instruction related to a handle, but it can also call
   * dispose method (if new version is incorrect) or
   * init handle (if the previous one was incorrect).
   *
   * @param an_old_line the previous structure
   * @param the_next_line a next line, necessary if new handle must be generated
   * @param a_classgen a class generator from BCEL
   * @param an_ins a BCEL instruction (to generate handle)
   * @param a_meth_end <code>true</code> if the line is the last one of the
   *   method
   * @param the_last TODO
   * @param the_instructions an array from {@ref BytecodeController} that the
   *   line is included
   * @param an_off an offset in this array
   */
  public final void update(final BytecodeLineController an_old_line,
                           final BytecodeLineController the_next_line,
                           final ClassGen a_classgen,
                           final Instruction an_ins,
                           final boolean a_meth_end,
                           final boolean the_last,
                           final LinkedList the_instructions,
                           final int an_off) {
    UmbraPlugin.messagelog("oldline=" + an_old_line.getMy_line_text());
    UmbraPlugin.messagelog("nextline=" + the_next_line.getMy_line_text());
    UmbraPlugin.messagelog("cg=" + ((a_classgen == null) ? "null" : "ok"));
    UmbraPlugin.messagelog("ins=" + ((an_ins == null) ? "null" :
                                                        an_ins.getName()));
    UmbraPlugin.messagelog("MetEnd=" + a_meth_end);
    UmbraPlugin.messagelog("theLast=" + the_last);
    UmbraPlugin.messagelog("off=" + an_off);
    my_methodgen = an_old_line.getMethod();
    my_instr_list = an_old_line.getList();
    my_instr_handle = an_old_line.getHandle();
    setIndex(an_old_line.getIndex());
    UmbraPlugin.messagelog("my_instr_handle=" + ((my_instr_handle == null) ?
                           "null" :
                           ((my_instr_handle.getInstruction() == null) ?
                           "null ins" :
                           my_instr_handle.getInstruction().getName())));
    if (my_instr_list == null) UmbraPlugin.messagelog("my_instr_list = null");
    else printInstructionList(my_instr_list);
    if (my_instr_handle == null) {
      UmbraPlugin.messagelog("A");
      initHandle(the_next_line, a_classgen, an_ins, a_meth_end,
                 the_instructions, an_off);
    } else if (my_instr_handle.getInstruction() == null) {
      UmbraPlugin.messagelog("B");
      initHandle(the_next_line, a_classgen, an_ins, a_meth_end,
                 the_instructions, an_off);
    } else if (an_ins != null) {
      UmbraPlugin.messagelog("C");
      my_instr_handle.setInstruction(an_ins);
      UmbraPlugin.messagelog("");
      updateMethod(a_classgen);
      the_instructions.set(an_off, this);
    } else {
      UmbraPlugin.messagelog("D");
      dispose(the_next_line, a_classgen, the_last, the_instructions, an_off);
    }
  }

  /**
   * Replacing BCEL method with the new one with updated
   * instruction list.
   *
   * @param a_classgen a class generator from BCEL
   */
  private void updateMethod(final ClassGen a_classgen) {
    final Method oldMet = a_classgen.getMethodAt(getIndex());
    a_classgen.replaceMethod(oldMet, my_methodgen.getMethod());
    //UmbraPlugin.messagelog(cg.getMethodAt(my_index).getCode().toString());
  }

  /**
   * @return the BCEL handle to the current instruction.
   */
  public final InstructionHandle getHandle() {
    return my_instr_handle;
  }

  /**
   * @return the BCEL list of the instructions in the method that contains
   * the current instruction.
   */
  public final InstructionList getList() {
    return my_instr_list;
  }

  /**
   * @return the method in which the current instruction is located
   */
  public final MethodGen getMethod() {
    return my_methodgen;
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
   * This method removes the current instruction line from BCEL structures.
   *
   * @param the_next_line the line after the removed one; it becomes a target of
   *   any jump instruction directed to the removed one
   * @param a_classgen a class generator from BCEL, this should be the same as
   *   in the {@ref BytecodeDocument} object for the currently edited
   *   bytecode file
   * @param the_last currently not used
   * @param the_instructions an array from {@ref BytecodeController} that
   *   contains the current line
   * @param an_off an offset in the <code>the_instructions</code> array which
   *   points to the instruction to be removed
   */
  public final void dispose(final BytecodeLineController the_next_line,
                            final ClassGen a_classgen,
                            final boolean the_last,
                            final LinkedList the_instructions,
                            final int an_off) {
    final InstructionHandle me = getHandle();
    final InstructionHandle next = the_next_line.getHandle();
    UmbraPlugin.messagelog("InstructionLineController#dispose   my_name=" +
                           getName());
    final InstructionTargeter[] tgters = my_instr_handle.getTargeters();
    if (tgters != null)
      for (int i = 0; i < tgters.length; i++) {
        tgters[i].updateTarget(me, next);
      }
    try {
      my_instr_list.delete(my_instr_handle);
    } catch (TargetLostException e) {
      //This should not happen as the instruction my_instr_handle has been
      //retargeted
      UmbraPlugin.messagelog("IMPOSSIBLE: dispose generated exception " +
                             "in InstructionLineController.dispose(...)");
    }
    my_instr_handle = null;
    my_methodgen.setInstructionList(my_instr_list);
    updateMethod(a_classgen);
    UmbraPlugin.messagelog("I am here");
    the_instructions.remove(an_off);
    printInstructionList(my_instr_list);
    UmbraPlugin.messagelog("Done");
  }

  /**
   * Replaces some words in a string with single characters.
   * Each of the letters in the returned word means that in the original line
   * there was the same character (if it belongs to string
   * {@link #SKIP_CHARS SKIP_CHARS}) or a corresponding word
   * listed below (otherwise):
   * <ul>
   * <li> C means a string within double quotes
   * <li> W means one or more following whitespaces
   * <li> D means a natural number
   * <li> X means any other word
   * </ul>
   * @param a_line  processing string
   * @return line with each (maximal) word from list above
   * (excluding characters from {@link #SKIP_CHARS SKIP_CHARS}) replaced with
   * corresponding character
   */
  private static String typ(final String a_line) {
    String s = "";
    boolean b;
    final String line = a_line + "|";
    for (int i = 0; i < line.length();) {
      b = false;
      for (int j = 0; j < SKIP_CHARS_LEN; j++)
        if (SKIP_CHARS.charAt(j) == line.charAt(i)) {
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
   * TODO rewrite the description
   *
   * @param a_pattern a string to compare
   * @param a_type a class of acceptable strings
   * @return <code>true</code> if <code>a_pattern</code> is one of strings
   *   from the type <code>a_type</code>, <code>false</code> otherwise
   */
  private static boolean compare(final String a_pattern, final String a_type) {
    if (a_pattern.equals(a_type))
      return true;
    if ((a_pattern.length() == 0) || (a_type.length() == 0))
      return false;
    if (a_type.startsWith("?{")) {
      final int n = a_type.indexOf("}");
      if (n > RBRACE_AFTER)
        if (compare(a_pattern, a_type.substring(n + 1)))
          return true;
      return compare(a_pattern, a_type.substring(RBRACE_AFTER, n) +
                     a_type.substring(n + 1));
    }
    if (a_type.startsWith("?"))
      return (compare(a_pattern, a_type.substring(1)) ||
              ((a_type.length() > 1) && compare(a_pattern,
                                              a_type.substring(RBRACE_AFTER))));
    if (a_pattern.charAt(0) != a_type.charAt(0))
      return false;
    return compare(a_pattern.substring(1), a_type.substring(1));
  }

  /**
   * Compares line with a pattern.
   * @param a_line a line of bytecode (with removed all comments)
   * @param a_type the type pattern in the fashion generated by
   *   the {@ref #typ(String)} method
   * @return <code>true</code> if <code>a_line</code> matches the pattern in
   *   <code>a_type</code>,
   *   <code>false</code> otherwise
   */
  public final boolean chkcorr(final String a_line, final String a_type) {
    final boolean b = compare(typ(a_line), "?D:?WX" + a_type + "|");
    return b;
  }

  /**
   * @param a_name the name to set
   */
  protected void setName(final String a_name) {
    my_name = a_name;
  }

  /**
   * @return the my_name
   */
  protected String getName() {
    return my_name;
  }
}
