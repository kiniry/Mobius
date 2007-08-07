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

import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

import umbra.UmbraPlugin;

/**
 * This is completely abstract class that contains some information
 * useful when the line is modified or BCEL structure is created.
 * Most details are implemented in subclasses.
 *
 * Methods of this class should operate on the {@ref ClassGen}
 * object which is located in the {@ref BytecodeDocument} object
 * that describes the state of the bytecode editor which contains
 * the line that corresponds to an object of the current class.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class BytecodeLineController {

  /**
   * The number of the method that contains the current line.
   * This is an index in the {@ref ClassGen} object in the
   * {@ref BytecodeDocument} object
   * that describes the state of the bytecode editor which contains
   * the line that corresponds to the current object.
   */
  private int my_index;

  /**
   * The string representation of the line in the bytecode file that contains
   * the current instruction. We assume that the comments have been stripped
   * off the line.
   */
  private String my_line_text;

  /**
   * TODO.
   *
   * @param a_line the string representation of the line in the bytecode
   *               document
   */
  public BytecodeLineController(final String a_line) {
    super();
    my_line_text = a_line;
  }

  /**
   * The method adds the link between the Umbra representation of
   * instructions to their representation in BCEL. In case the
   * line does not correspond to an instruction we only register
   * the number of the method the line is associated with.
   *
   * @param an_ihandle the BCEL instruction handle that corresponds to the
   *       instruction associated with the current object
   * @param a_ilist the list of instructions in the current method
   * @param a_methodgen the object which represents the method of the current
   *    instruction in the BCEL representation of the current class
   *    in the bytecode editor
   * @param an_index method number in the current class
   * @return true when the current line corresponds to an instruction, false
   *     otherwise
   */
  public boolean addHandle(final InstructionHandle an_ihandle,
               final InstructionList a_ilist,
               final MethodGen a_methodgen,
               final int an_index) {
    my_index = an_index;
    return false;
  }

  /**
   * This method is redefined in each subclass of particular
   * instruction type. It is used for creating a handle
   * containing appropriate BCEL instruction object
   * that matches with the instruction name.
   *
   * @return Handle to the appropriate instruction;
   *   null if the line is not an instruction one.
   */
  public Instruction getInstruction() {
    return null;
  }


  /**
   * TODO.
   *
   * @param an_ilist TODO
   * @param an_ins TODO
   */
  public void setTarget(final InstructionList an_ilist,
                        final Instruction an_ins) {

  }

  /**
   * TODO.
   *
   * @param the_next_line TODO
   * @param a_classgen a {@ref ClassGen} object in the {@ref BytecodeDocument}
   *        object that describes the state of the bytecode editor which
   *        contains the line that corresponds to the current object.
   * @param an_ins TODO
   * @param a_methend_flag TODO
   * @param the_instructions TODO
   * @param an_off TODO
   */
  public void initHandle(final BytecodeLineController the_next_line,
                         final ClassGen a_classgen,
                         final Instruction an_ins,
                         final boolean a_methend_flag,
                         final LinkedList the_instructions,
                         final int an_off) {
  }

  /**
   * TODO.
   *
   * @param the_old_line TODO
   * @param the_next_line TODO
   * @param a_classgen a {@ref ClassGen} object in the {@ref BytecodeDocument}
   *        object that describes the state of the bytecode editor which
   *        contains the line that corresponds to the current object.
   * @param an_ins TODO
   * @param a_methend_flag TODO
   * @param the_last_flag TODO
   * @param the_instructions TODO
   * @param an_off TODO
   */
  public void update(final BytecodeLineController the_old_line,
                     final BytecodeLineController the_next_line,
                     final ClassGen a_classgen,
                     final Instruction an_ins,
                     final boolean a_methend_flag,
                     final boolean the_last_flag,
                     final LinkedList the_instructions,
                     final int an_off) {
    if (the_old_line.getHandle() != null) { //in case this was an instruction
                                            //before
      the_old_line.dispose(the_next_line, a_classgen, the_last_flag,
                           the_instructions, an_off);
    }
  }

  /**
   * TODO.
   *
   * @return TODO
   */
  public InstructionHandle getHandle() {
    return null;
  }

  /**
   * TODO.
   *
   * @return TODO
   */
  public InstructionList getList() {
    return null;
  }

  /**
   * TODO.
   *
   * @return TODO
   */
  public MethodGen getMethod() {
    return null;
  }

  /**
   * TODO.
   *
   * @return TODO
   */
  public final int getIndex() {
    return my_index;
  }



  /**
   * This method is used to check some basic condition of
   * correctness. For non-instruction line this is the only
   * checking. It is usually redefined in the subclasses so that
   * if it returns true the line is regarded to be correct.
   *
   * @return  true if the instruction is correct
   * @see    InstructionLineController#correct()
   */
  public boolean correct()  {
    return false;
  }

  /**
   * TODO.
   *
   * @param the_next_line TODO
   * @param a_classgen a {@ref ClassGen} object in the {@ref BytecodeDocument}
   *       object that describes the state of the bytecode editor which contains
   *       the line that corresponds to the current object.
   * @param the_last TODO
   * @param the_instructions an array with instruction representations. These
   * are represented as objects the classes of which are subclasses of
   * {@ref InstructionLineController}.
   * @param an_off TODO
   */
  public void dispose(final BytecodeLineController the_next_line,
            final ClassGen a_classgen,
            final boolean the_last,
            final LinkedList the_instructions, final int an_off) {
    UmbraPlugin.messagelog("dispose(BytecodeLineController)" +
                           ((InstructionLineController)(the_instructions.
                                        get(an_off))).
                                        getHandle().getInstruction().getName());
  }

  /**
   * TODO.
   *
   * @param an_index TODO
   */
  public void setIndex(final int an_index) {
    my_index = an_index;
  }

  /**
   * The method returns the String representation of the current instruction
   * content.
   *
   * @return the representation of the line
   */
  public final String getLineContent() {
    return my_line_text;
  }

  /**
   * @return the line of the text with the bytecode line
   */
  public String getMy_line_text() {
    return my_line_text;
  }
}
