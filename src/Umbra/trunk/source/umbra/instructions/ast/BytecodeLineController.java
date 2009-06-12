/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import java.util.HashMap;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

import annot.bcclass.BCMethod;

import umbra.instructions.InstructionParser;
import umbra.lib.UmbraException;

/**
 * This is completely abstract class that contains some information
 * useful when the line is modified or BCEL structure is created.
 * Most details are implemented in subclasses.
 *
 * Methods of this class should operate on the
 * {@link org.apache.bcel.generic.ClassGen}
 * object which is located in the {@link umbra.editor.BytecodeDocument} object
 * that describes the state of the byte code editor which contains
 * the line that corresponds to an object of the current class.
 *
 * Note that some methods which logically belong to
 * {@link InstructionLineController} are defined already here. This is caused
 * by the fact that some of the line controllers may be associated with a
 * method even though they do not handle instructions (but e.g. comments
 * or empty lines).
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public abstract class BytecodeLineController {

  /**
   * The constant returned that the byte code line cannot be assigned a
   * meaningful position inside a method.
   */
  public static final int WRONG_POSITION_IN_METHOD = -2;

  /**
   * This is an object contains a parser which allows to check the
   * correctness of the byte code line and to parse its parameters.
   */
  private InstructionParser my_parser;

  /**
   * The number of the method that contains the current line.
   * This is an index in the {@link org.apache.bcel.generic.ClassGen} object
   * available through the {@link umbra.editor.BytecodeDocument} object
   * that describes the state of the byte code editor which contains
   * the line that corresponds to the current object.
   *
   * Values not less than zero mean the line is associated with a method.
   * Values less than zero mean the line is not associated with any method.
   */
  private int my_methodno;

  /**
   * The string representation of the line in the byte code file that contains
   * the current instruction. We assume that the comments have been stripped
   * off the line. The line text does not change in the lifetime of the object.
   */
  private String my_line_text;

  /**
   * This constructor creates the controller with the given content of the
   * line it handles. It also creates the local parser which handles the
   * parsing of the content of the line and initialises the association with
   * a method so that no method is associated with the line controller.
   *
   * @param a_line the string representation of the line in the byte code
   *   document
   */
  public /*@ pure @*/ BytecodeLineController(final String a_line) {
    super();
    my_line_text = a_line;
    my_parser = new InstructionParser(a_line);
    my_methodno = -1;
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
   *    in the byte code editor
   * @return true when the current line corresponds to an instruction, false
   *     otherwise
   */
  public boolean addHandle(final InstructionHandle an_ihandle,
               final InstructionList a_ilist,
               final MethodGen a_methodgen) {
    return false;
  }

  /**
   * This method is redefined in each subclass of particular
   * instruction type. It is used for creating a handle
   * containing appropriate BCEL instruction object
   * that matches with the instruction name.
   *
   * @return handle of the type {@link Instruction} to the appropriate
   *   instruction or <code>null</code> if the line is not an instruction one.
   */
  public Instruction getInstruction() {
    return null;
  }


  /**
   * Sets the target of the given instruction.
   * This method is used to provide a common interface for all the instructions,
   * but the actual work is done only in case of the jump instructions. Here
   * it does nothing.
   *
   * @param an_ilist an instruction list with the jump instruction
   * @param an_ins the instruction to set the target for
   * @throws UmbraException when the instruction has improper target
   * @see umbra.instructions.ast.BytecodeLineController#setTarget(
   *                            org.apache.bcel.generic.InstructionList,
   *                            org.apache.bcel.generic.Instruction)
   */
  public void setTarget(final InstructionList an_ilist,
                        final Instruction an_ins) throws UmbraException {
  }

  /**
   * Returns the {@link InstructionList} structure in which the current
   * instruction is located. In case of {@link BytecodeLineController}, this
   * method always returns <code>null</code>.
   *
   * @return the BCEL list of the instructions of the method to which the
   *   current instruction belongs
   */
  public InstructionList getList() {
    return null;
  }

  /**
   * Returns the {@link BCMethod} structure responsible for the method in
   * which the instruction resides. In case of {@link BytecodeLineController}
   * this method always returns <code>null</code>.
   *
   * @return the method in which the current instruction is located
   */
  public BCMethod getMethod() {
    return null;
  }

  /**
   * Return the method number of the method in which the line is located. For
   * lines that are not associated with any method this is equal to -1.
   *
   * @return method number
   */
  public final int getMethodNo() {
    return my_methodno;
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
   * This method sets the number of the method which the current line belongs
   * to. Normally, the number is not less than 0. The value -1 means the line
   * is not associated with any method.
   *
   * @param an_index number of the method
   */
  public void setMethodNo(final int an_index) {
    my_methodno = an_index;
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
   * @return the line of the text with the byte code line
   */
  public String getMy_line_text() {
    return my_line_text;
  }

  /**
   * @return the line parser for the current line
   */
  protected InstructionParser getParser() {
    return my_parser;
  }

  /**
   * Checks if the line can be an end of comment. End of comment line can only
   * be of {@link AnnotationLineController} type so the default behaviour is
   * to always return false.
   *
   * @return <code>true</code> when the line contains the end of comment
   *   sequence, <code>false</code> otherwise
   */
  public boolean isCommentEnd() {
    return false;
  }

  /**
   * Checks is the line can be an end of a comment.
   *
   * @return <code>true</code> when the line contains the end of comment
   *   sequence, <code>false</code> otherwise
   */
  public boolean isCommentStart() {
    return getMy_line_text().contains("/*");
  }

  /**
   * This method returns the number of the instruction handled by the current
   * line controller. If no instruction can be associated with the line
   * the value -2 is returned. In case of {@link BytecodeLineController},
   * this method always returns -2.
   *
   * @return the number of the instruction or -2 in case the number cannot
   *   be determined
   */
  public int getNoInMethod() {
    return WRONG_POSITION_IN_METHOD;
  }

  /**
   * Returns <code>true</code> when a BCEL method representation must be
   * associated with the current line controller. The default result
   * is <code>false</code>.
   *
   * @return <code>true</code> when a BCEL method representation must be
   *   associated with the current line controller, otherwise
   *   <code>false</code>
   */
  public boolean needsMg() {
    return false;
  }

  /**
   * Returns <code>true</code> when a BCEL method representation is
   * associated with the current line controller. The default result
   * is <code>false</code>.
   *
   * @return <code>true</code> when a BCEL method representation is
   *   associated with the current line controller, otherwise <code>false</code>
   */
  public boolean hasMg() {
    return false;
  }

  /**
   * This method instructs the line controller to remove the BCEL item
   * associated with it from the BCEL representation of the class. The generic
   * implementation does nothing.
   */
  public void removeFromBCEL() {
  }

  /**
   * This method instructs the line controller to add the BCEL item
   * associated with it to the BCEL representation of the class. The generic
   * implementation does nothing.
   *
   * @throws UmbraException in case the representation does not allow to
   *   add the content of the line to BML and BCEL representation
   */
  public void addToBCEL() throws UmbraException {
  }

  /**
   * Checks the equality of the current BytecodeLineController and the
   * one given in the argument. The equality holds when the controllers
   * are both of the same class and represent the same string.
   *
   * @param an_o an object to check the equality with
   * @return <code>true</code> in case the object is equal to the current
   *   line controller, <code>false</code> otherwise
   */
  @Override
  public boolean equals(final Object an_o) {
    if (an_o.getClass().equals(this.getClass())) {
      final BytecodeLineController bc = (BytecodeLineController) an_o;
      return my_line_text.trim().equals(bc.getLineContent().trim());
    }
    return false;
  }

  /**
   * The hash code for the current line controller.
   *
   * @return the value of the hash is just the hash code of the trimmed line
   *   string
   */
  @Override
  public int hashCode() {
    return my_line_text.trim().hashCode();
  }

  /**
   * Returns "clean" number for a given "dirty" one. If there is no such
   * "dirty" number (there is no constant with that number in textual bytecode
   * representation) size of constant pool + 1 is returned. <br>
   * Note: this method was inserted to BytecodeLineController to make it visible
   * for both instruction and constant pool subclasses.
   *
   * @param a_map a map that maps "dirty" numbers onto "clean" ones; the map
   * should contain size of the constant pool at the key -1
   * @param a_num "dirty" number
   * @return "clean" number corresponding to a given "dirty" one
   *
   * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
   */
  protected int dirtyToClean(final HashMap a_map, final int a_num) {
    if (a_map.containsKey(a_num)) return (Integer) a_map.get(a_num);
    return (Integer) a_map.get(-1) + 1;
  }

}
