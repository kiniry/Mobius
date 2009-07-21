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

import umbra.UmbraPlugin;
import umbra.instructions.ast.BytecodeLineController;

/**
 * This class contains various helper methods that are used in the
 * {@link BytecodeController} class. It also keeps track of the incorrect
 * lines and the modified lines.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
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
   * The field is first intialised to be <code>null</code>.
   * This field is initialised by a separate method - not within the
   * constructor.
   */
  private boolean[] my_modified;

  /**
   * This constructor initialises the internal container of the incorrect lines
   * to be empty. The  structures to keep track of the modified lines are
   * left uninitialised.
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
    @ requires FileNames.DEBUG_MODE;
    @*/
  /**
   * This method prints out to the standard output the
   * list of all the incorrect instructions in the controller. We assume the
   * calls to this method are guarded by checks of
   * {@link umbra.lib.FileNames#DEBUG_MODE}.
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
   * Returns the information about the correctness of the method bodies in
   * the current controller.
   *
   * @return <code>true</code> when the method bodies are syntactically correct
   *   and <code>false</code> otherwise
   */
  public boolean bodyCorrect() {
    return allCorrect();
  }

  /**
   * Returns a 0-based number of the line with the first error.
   *
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
   * code level. See {@link umbra.editor.actions.BytecodeCombineAction}. The
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
