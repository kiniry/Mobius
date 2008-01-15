/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
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
  public /*@ pure @*/ InstructionLineController(final String a_line_text,
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
          // TODO: this report should look like differently
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
   * This method is executed when a line is modified
   * but not inserted or removed. It usually replaces BCEL
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
    my_methodgen = an_old_line.getMethod();
    my_instr_list = an_old_line.getList();
    my_instr_handle = an_old_line.getHandle();
    setIndex(an_old_line.getIndex());
    if (my_instr_handle == null) {
      initHandle(the_next_line, a_classgen, an_ins, a_meth_end,
                 the_instructions, an_off);
    } else if (my_instr_handle.getInstruction() == null) {
      initHandle(the_next_line, a_classgen, an_ins, a_meth_end,
                 the_instructions, an_off);
    } else if (an_ins != null) {
      my_instr_handle.setInstruction(an_ins);
      updateMethod(a_classgen);
      the_instructions.set(an_off, this);
    } else {
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
   *   the current instruction
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
  public boolean correct() {
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
    the_instructions.remove(an_off);
    printInstructionList(my_instr_list);
  }

  /**
   * @param a_name the mnemonic name to set
   */
  protected void setName(final String a_name) {
    my_name = a_name;
  }

  /**
   * @return the name of the mnemonic
   */
  protected String getName() {
    return my_name;
  }

  /*@
    @ ensures \result ==> getParser().isInitialised();
    @*/
  /**
   * This method parses initial part of a instruction line. This is a helper
   * method which parses the common part of each instruction line i.e.:
   *
   *  whitespace number : whitespace
   *
   * @return <code>true</code> when all the parsing is done sucessfully,
   *   <code>false</code> in case the initial portion of the line is not of
   *   the required form
   */
  protected boolean parseTillMnemonic() {
    boolean res = true;
    final InstructionParser parser = getParser();
    parser.resetParser();
    res = parser.swallowWhitespace();
    res = res && parser.swallowNumber(); //line number
    res = res && parser.swallowDelimiter(':'); // :
    res = res && parser.swallowWhitespace(); //whitespace before mnemonic
    return res;
  }
}
