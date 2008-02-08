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

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;

import umbra.UmbraPlugin;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.InstructionLineController;

/**
 * @author alx
 * @version a-01
 *
 */
public abstract class BytecodeControllerHelper {

  /**
   * The list of all the lines which were detected to be incorrect.
   */
  private LinkedList my_incorrect;

  /**
   * Keeps track of modified methods. Each time a method is modified
   * an entry with the method number is marked <code>true</code> in the array.
   * The field is first intialised to be <code>null</code>. It is first
   * filled with values by the
   * {@link #init(BytecodeDocument, String[], String[])} method.
   * This field is initialised by a separate method - not within the
   * constructor.
   */
  private boolean[] my_modified;

  /**
   * This method initialises the internal container of the incorrect lines
   * to be empty.
   */
  protected BytecodeControllerHelper() {
    my_incorrect = new LinkedList();
  }

  /**
   * This is a debugging method. It prints out to the standard output the
   * all the controllers in the given list.
   *
   * @param the_list the list of line controllers
   */
  public static void showEditorLines(final LinkedList the_list) {
    for (int i = 0; i < the_list.size(); i++) {
      UmbraPlugin.LOG.print(
                ((BytecodeLineController)(the_list.get(i))).
                                  getMy_line_text());
    }
  }

  /*@
    @ requires UmbraHelper.DEBUG_MODE;
    @*/
  /**
   * This method prints out to the standard output the
   * list of all the incorrect instructions in the controller. We assume the
   * calls to this method are guarded by checks of
   * {@link umbra.UmbraHelper#DEBUG_MODE}.
   *
   * @param the_list the list of controllers to present as incorrect ones
   */
  public static void showAllIncorrectLines(final LinkedList the_list) {
    UmbraPlugin.messagelog("showAllIncorrectLines" + the_list.size() +
                           " incorrects:");
    for (int i = 0; i < the_list.size(); i++) {
      UmbraPlugin.messagelog(" " +
           ((BytecodeLineController)(the_list.get(i))).getMy_line_text());
    }
  }


  /**
   * This is a helper method used for debugging purposes. It prints out
   * all the instructions in the internal Umbra representation of a class
   * file.
   *
   * @param the_instructions the instructions which are printed out
   * @param an_index the number which allows to make different printouts
   */
  public static void controlPrint(final LinkedList the_instructions,
                                  final int an_index) {
    UmbraPlugin.messagelog("");
    UmbraPlugin.messagelog("Control print of bytecode modification (" +
                           an_index + "):");
    for (int i = 0; i < the_instructions.size(); i++) {
      final InstructionLineController line =
                            (InstructionLineController)the_instructions.get(i);
      if (line == null) {
        UmbraPlugin.messagelog("" + i + ". null");
        return;
      }
      //if (line.index == index) {
      UmbraPlugin.messagelog("" + i + ". " + line.getName());
      final InstructionHandle ih = line.getHandle();
      if (ih == null) UmbraPlugin.messagelog("  handle - null");
      else {
        UmbraPlugin.LOG.print("  handle(" + ih.getPosition() + ") ");
        final Instruction ins = ih.getInstruction();
        if (ins == null) UmbraPlugin.LOG.print("null instruction");
        else UmbraPlugin.LOG.print(ins.getName());
        if (ih.getNext() == null) UmbraPlugin.LOG.print(" next: null");
        else UmbraPlugin.LOG.print(" next: " + ih.getNext().getPosition());
        if (ih.getPrev() == null) UmbraPlugin.messagelog(" prev: null");
        else UmbraPlugin.messagelog(" prev: " + ih.getPrev().getPosition());
      }
      //}
    }
  }


  /**
   * The method removes from the collection of the incorrect lines
   * all the lines which are between <code>a_start</code> and
   * <code>a_stop</code>.
   *
   * @param a_start the first line which is checked for removing
   * @param a_stop the last line which is checked for removing
   */
  public void removeIncorrects(final int a_start, final int a_stop) {
    for (int i = a_start; i <= a_stop; i++) {
      final BytecodeLineController line = getLineController(i);
      if (my_incorrect.contains(line)) {
        my_incorrect.remove(line);
      }
    }
  }

  /**
   * @return <code>true</code> if there is no incorrect line within the whole
   *         document
   */
  public boolean allCorrect() {
    return my_incorrect.isEmpty();
  }


  /**
   * @return number of a line that the first error occurs
   * (not necessarily: number of the first line that an error occurs)
   */
  public int getFirstError() {
    return getLineControllerNo((BytecodeLineController)my_incorrect.getFirst());
  }

  /**
   * Adds at the end of the  incorrect lines list the given line controller.
   *
   * @param a_bcl the controller to add
   */
  protected void addIncorrect(final BytecodeLineController a_bcl) {
    my_incorrect.addLast(a_bcl);
  }

  /**
   * Returns the line controller for the given line.
   *
   * @param a_lineno the line number of the retrieved controller line
   * @return the controller line for the given line number
   */
  protected abstract BytecodeLineController getLineController(
                                                  final int a_lineno);

  /**
   * Returns the line number for the given line.
   *
   * @param a_line the line controller for which we obtain the number of line
   * @return the number of line for the given controller or -1 if there is no
   *   such a line
   */
  protected abstract int getLineControllerNo(
                                      final BytecodeLineController a_line);


  /**
   * Marks given method as modified.
   *
   * @param a_methno the number of the marked method
   */
  protected void markModified(final int a_methno) {
    my_modified[a_methno] = true;
  }


  /**
   * Returns the information on which methods were modified in the editor. This
   * is used to enable the possibility to replace the code of the methods
   * modified on the source code level, but that were not modified at the byte
   * code level. See {@link umbra.editor.actions. BytecodeCombineAction}. The
   * returned array has <code>true</code> in entries that correspond to modified
   * methods and <code>false</code> otherwise.
   *
   * @return the array with information on modified methods.
   */
  public boolean[] getModified() {
    return my_modified;
  }


  /**
   * @param the_modified the array that indicates which methods were modified
   */
  public void setModified(final boolean[] the_modified) {
    this.my_modified = the_modified;
  }


  /**
   * This method causes the initialisation of the table which keeps track
   * of the modified methods.
   *
   */
  public void initModTable() {
    my_modified = null;
  }

  /**
   * Fills in the structure which keeps track of the modified methods.
   *
   * @param a_methodnum the number of the method to modify
   */
  protected void fillModTable(final int a_methodnum) {
    if (my_modified == null) {
      my_modified = new boolean[a_methodnum];
      for (int a_method_count = 0; a_method_count < my_modified.length;
           a_method_count++)
        my_modified[a_method_count] = false;
    }
  }

}
