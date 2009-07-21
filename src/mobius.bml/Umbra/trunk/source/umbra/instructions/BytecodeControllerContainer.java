/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;

import umbra.UmbraPlugin;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.ThrowsLineController;
import umbra.lib.FileNames;
import umbra.lib.UmbraException;

/**
 * This class encapsulates the structure of the subsequent editor lines of the
 * {@link BytecodeController} and gives the external interface to them.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public abstract class BytecodeControllerContainer extends
    BytecodeControllerComments {


  /**
   * The list of all the lines in the current byte code editor. These lines
   * are stored as objects the classes of which are subclasses of
   * {@link BytecodeLineController}.
   */
  private LinkedList my_editor_lines;
  //@ invariant !my_editor_lines.containsNull;
  /*@ invariant (\forall int i; 0 <= i && i < my_editor_lines.size();
    @            my_editor_lines.get(i) instanceof BytecodeLineController);
    @*/

  /**
   * This object maps the references to constant pool entries in BCEL
   * representation of bytecode onto editor lines that represents that entries
   * (for constants having such editor line) and references to constant pool
   * entries that was generated automatically when new field was added
   * from those fields.
   */
  private BytecodeMapping my_mapping;

  /**
   * The constructor does only the initialisation of the superclass. It does
   * no initalisation. The initialisation should be done in the
   * initialisation method.
   */
  public BytecodeControllerContainer() {
    super();
    my_mapping = new BytecodeMapping();
  }

  /**
   * Returns the line controller for the given line.
   *
   * @param a_lineno the line number of the retrieved controller line
   * @return the controller line for the given line number
   */
  public final BytecodeLineController getLineController(final int a_lineno) {
    return (BytecodeLineController)my_editor_lines.get(a_lineno);
  }

  /**
   * Returns the line number for the given line.
   *
   * @param a_line the line controller for which we obtain the number of line
   * @return the number of line for the given controller or -1 if there is no
   *   such a line
   */
  protected final int getLineControllerNo(final BytecodeLineController a_line) {
    return my_editor_lines.indexOf(a_line);
  }

  /**
   * Replaces the line controller at the given position with the given
   * new line controller.
   *
   * @param a_pos the position of the line controller to be replaced
   * @param a_newlc the new line controller
   */
  protected final void replaceLineController(final int a_pos,
                                        final BytecodeLineController a_newlc) {
    my_editor_lines.remove(a_pos);
    my_editor_lines.add(a_pos, a_newlc);
  }

  /**
   * Insertst the given line controller at the given position. The instruction
   * at the postion <code>a_pos</code> and all instructions after that are
   * shifted to the right (i.e. their indicies are incremented).
   *
   * @param a_pos the position at which the controller is inserted
   * @param a_lc the controller to be inserted
   */
  protected final void insertEditorLine(final int a_pos,
                                        final BytecodeLineController a_lc) {
    my_editor_lines.add(a_pos, a_lc);
  }

  /**
   * Returns the last annotation line for the annotation lines block
   * starting with the given postion. We assume the given postion
   * points to an {@link AnnotationLineController}.
   *
   * @param a_pos a postion with an annotation line controller
   * @return the postion of the last annotation line controller in the current
   *   block
   */
  protected final int getAnnotationEnd(final int a_pos) {
    for (int i = a_pos; i < my_editor_lines.size(); i++) {
      if (!(getLineController(i) instanceof AnnotationLineController)) {
        return i - 1;
      }
    }
    return my_editor_lines.size() - 1;
  }

  /**
   * Returns the total number of the lines in the current document.
   *
   * @return the number of lines in the current document
   */
  public int getNoOfLines() {
    return my_editor_lines.size();
  }

  /**
   * Returns the line number corresponding to the line with the given
   * program counter value in the method of the given number. In case there
   * is no such method or no such program counter in an existing method then
   * -1 is returned.
   *
   * @param a_pc the program counter of the instruction for which we look for
   *   the line number
   * @param a_mno the method number
   * @return the line number of the line with the given pc in the given method
   */
  public int getLineForPCInMethod(final int a_pc, final int a_mno) {
    BytecodeLineController elem;
    final Iterator i = my_editor_lines.iterator();
    int pos = seekMethodForNumber(a_mno, i);
    while (i.hasNext()) {
      elem = (BytecodeLineController)i.next();
      pos++;
      if (!(elem instanceof ThrowsLineController)) {
        while (i.hasNext()) {
          if (elem instanceof InstructionLineController) {
            final InstructionLineController ielem =
                             (InstructionLineController) elem;
            if (ielem.getLineContent().startsWith(a_pc + ":")) {
              return pos;
            }
          } else {
            if (elem instanceof HeaderLineController) {
              break;
            }
          }
          elem = (BytecodeLineController)i.next();
          pos++;
        }
        break;
      }
    }
    return -1;
  }

  /**
   * Returns the line number corresponding to the last line with an instruction
   * in the method of the given number. In case there
   * is no such method or no such line in the method then
   * -1 is returned.
   *
   * @param a_mno the method number
   * @return the line number of the line with the given pc in the given method
   */
  public int getLastLineInMethod(final int a_mno) {
    BytecodeLineController elem;
    final Iterator i = my_editor_lines.iterator();
    int pos = seekMethodForNumber(a_mno, i);
    int lastinspos = -1;
    while (i.hasNext()) {
      elem = (BytecodeLineController)i.next();
      pos++;
      if (!(elem instanceof ThrowsLineController)) {
        while (i.hasNext()) {
          if (elem instanceof InstructionLineController) {
            lastinspos = pos;
          } else if (elem instanceof HeaderLineController) {
            break;
          }
          elem = (BytecodeLineController)i.next();
          pos++;
        }
        break;
      }
    }
    return lastinspos;
  }
  /**
   * Retrieves the position of the method with the given number. It uses
   * the iterator to range over the editor lines and it moves it at the
   * header line of the method or to the end of the lines container in
   * case there is no method for the given number.
   *
   * @param a_mno a method number to look for
   * @param an_iter the iterator to traverse the editor lines
   * @return the line number of the header line or the number of lines -1 in
   *   case there is no given method
   */
  private int seekMethodForNumber(final int a_mno,
                                  final Iterator an_iter) {
    BytecodeLineController elem;
    int pos = -1;
    while (an_iter.hasNext()) {
      elem = (BytecodeLineController)an_iter.next();
      pos++;
      if (elem instanceof HeaderLineController) {
        final HeaderLineController helem = (HeaderLineController) elem;
        if (helem.getMethodNo() == a_mno) break;
      }
    }
    return pos;
  }

  /**
   * Returns the first line below the given one which in the current method
   * contains an instruction line. It consults all the lines starting with
   * the given one and checks if they are {@link InstructionLineController}.
   * In case one is, the index of the line is returned. In case a
   * {@link HeaderLineController} is reached or an end of the document
   * then the exception is thrown.
   *
   * @param a_line_no the line for which we look for an instruction line
   * @return the number of a line (in textual representation) which is
   *   the required instruction line
   * @throws UmbraException in case the current method has no instruction line
   *   below the given line
   */
  public int getInstructionLineBelow(final int a_line_no)
    throws UmbraException {
    for (int i = a_line_no; i < my_editor_lines.size(); i++) {
      final BytecodeLineController blc = getLineController(i);
      if (blc instanceof InstructionLineController) {
        return i;
      } else if (blc instanceof HeaderLineController) {
        throw new UmbraException();
      }
    }
    throw new UmbraException();
  }

  /**
   * This method gives the program counter for the given line. It gives the
   * correct number only in case the given line is indeed a line which
   * contains an instruction and in that case it returns the program
   * counter associated with its BCEL representation (not the label number
   * in the text of the document).
   *
   * @param a_lineno the number of the line to retrieve the program counter for
   * @return the program counter or -1 in case the program counter cannot
   *   be retrieved
   */
  public int getLabelForLine(final int a_lineno) {
    final BytecodeLineController blc = getLineController(a_lineno);
    if (blc instanceof InstructionLineController) {
      final InstructionLineController ilc = (InstructionLineController) blc;
      return ilc.getPC();
    }
    return -1;
  }

  /**
   * This method returns the string with the content of the current document
   * as a result of its internal representation.
   *
   * @return the string with the internal representation of the document
   */
  public String printDocument() {
    BytecodeLineController elem;
    final StringBuffer buf = new StringBuffer();
    for (final Iterator i = my_editor_lines.iterator(); i.hasNext();) {
      elem = (BytecodeLineController) i.next();
      buf.append(elem.getLineContent());
    }
    return buf.toString();
  }

  /**
   * The method initialises the editor lines of the controller.
   *
   * @param an_editorlines the list with all the editor lines
   */
  protected void init(final LinkedList an_editorlines) {
    my_editor_lines = an_editorlines;
  }

  /**
   * This method removes from the internal structures the lines of the region
   * from {@code a_start} to {@code a_stop} inclusively. This method
   * also removes the connection between the removed lines and the BCEL
   * representation of the byte code.
   * <br> <br>
   * It uses index to remove lines from my_editor_lines because
   * equals for EmptyLineController always returns true.
   *
   * @param a_start the first line to be removed
   * @param a_stop the last line to be removed
   * @throws UmbraException in case the structure of the editor lines is
   *   malformed
   */
  protected void removeEditorLines(final int a_start,
                                   final int a_stop)
    throws UmbraException {
    if (FileNames.CP_DEBUG_MODE) System.err.println("[[:: REMOVE ::]]");
    final ArrayList < Integer > delete_list = new ArrayList < Integer > ();
    for (int i = a_stop + 1; i <= a_start; i++) {
      try {
        final BytecodeLineController oldlc = getLineController(i);
        if (oldlc instanceof InstructionLineController) {
          ((InstructionLineController)oldlc).dispose();
        }
        if (FileNames.CP_DEBUG_MODE)
          System.err.println("<" + oldlc.getLineContent() + ">");
        delete_list.add(i);
      } catch (ClassCastException e) { // malformed internal structure
        UmbraPlugin.messagelog("IMPOSSIBLE: malformed structure of the " +
                               "editor lines");
        throw new UmbraException();
      }
    }
    int deleted = 0;
    for (Integer j : delete_list) {
      my_editor_lines.remove(j.intValue() - deleted);
      deleted++;
    }
  }

  /**
   * Returns the object that maps the references to constant pool entries in
   * BCEL representation of bytecode onto editor lines that represents that
   * entries (for constants having such editor line) and references to constant
   * pool entries that was generated automatically when new field was added
   * from those fields.
   *
   * @return the mapping object
   */
  public BytecodeMapping getMapping() {
    return my_mapping;
  }

}
