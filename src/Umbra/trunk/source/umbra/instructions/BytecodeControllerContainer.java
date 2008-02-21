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

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.InstructionLineController;

/**
 * This class encapsulates the internal structures of the
 * {@link BytecodeController} and gives the internal interface to them.
 *
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
   * The list of all the lines in the editor which contain codes of
   * instructions. These are represented as objects the classes of which
   * are subclasses of {@link InstructionLineController}.
   */
  private LinkedList my_instructions;

  /**
   * The constructor does only the initialisation of the superclass. It does
   * no initalisation. The initialisation should be done in the
   * {@link #init(BytecodeDocument, String[], String[])} method.
   */
  public BytecodeControllerContainer() {
    super();
  }
  /**
   * This method handles the initial parsing of a byte code textual document.
   * It creates a parser {@link InitParser} and runs it with the given
   * document and array with comments pertinent to the instruction lines.
   * Subsequently, it initialises the internal structures to handle editor
   * lines, instructions, comments, and modifications.
   *
   * @param a_doc the byte code document with the corresponding BCEL
   *   structures linked into it
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the document,
   *   if this parameter is null then the array is not taken into account
   * @param a_interline contains the texts of interline comments, the
   *   i-th entry contains the comment for the i-th line in the document,
   *   if this parameter is null then the array is not taken into account
   *   FIXME: currently ignored
   */
  public void init(final BytecodeDocument a_doc,
                   final String[] a_comment_array,
                   final String[] a_interline) {
    final InitParser initParser = new InitParser(a_doc, a_comment_array);
    initParser.runParsing();
    my_editor_lines = initParser.getEditorLines();
    my_instructions = initParser.getInstructions();
    initComments(initParser);
    int a_methodnum = 0;
    if (!my_instructions.isEmpty()) {
      a_methodnum = ((BytecodeLineController)my_instructions.getLast()).
                  getMethodNo() + 1;
    }
    fillModTable(a_methodnum);
    if (UmbraHelper.DEBUG_MODE) controlPrint(0);
  }

  /**
   * Returns the line controller for the given line.
   *
   * @param a_lineno the line number of the retrieved controller line
   * @return the controller line for the given line number
   */
  protected final BytecodeLineController getLineController(final int a_lineno) {
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
   * Returns the line controller for the given instruction number.
   * The instruction number is the sequence number of the instruction in
   * the textual file.
   *
   * @param an_insno the number of the retrieved instruction
   * @return the controller line for the given instruction number
   */
  protected final InstructionLineController getInstruction(final int an_insno) {
    return (InstructionLineController)my_instructions.get(an_insno);
  }

  /**
   * Returns the total number of the instructions in the current document.
   *
   * @return the number of instructions in the current document
   */
  protected final int getNoOfInstructions() {
    return my_instructions.size();
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
   * Finds the first instruction line controller in the given range of lines.
   *
   * @param the_first the first line to be checked
   * @param the_last the last line to be checked
   * @return the number of the line with the instruction line controller or -1
   *   in case there is no instruction line controller in the given range
   */
  protected final int getFirstInstructionInRegion(final int the_first,
                                                  final int the_last) {
    int first = -1;
    for (int i = the_first; i <= the_last; i++) {
      final BytecodeLineController o = getLineController(i);
      if (first < 0) {
        first = my_instructions.indexOf(o);
      }
      my_instructions.remove(o);
    }
    return first;
  }


  /**
   * Finds the first instruction line controller after the given point. The
   * line with the given number is included in the search.
   *
   * @param a_pos the position from which the search starts
   * @return the line number of the first position that is an instruction line,
   *   or -1 in case there is no instruction line after the given point
   */
  protected final int getFirstInstructionAfter(final int a_pos) {
    int first = -1;
    for (int i = a_pos + 1; i < my_editor_lines.size(); i++) {
      final BytecodeLineController o = getLineController(i);
      if (first < 0) {
        first = my_instructions.indexOf(o);
        if (first >= 0) break;
      }
    }
    return first;
  }

  /**
   * Adds the given list of instructions at the end of the local instruction
   * list.
   *
   * @param the_instructions the instructions to be added
   */
  protected final void appendInstructions(final LinkedList the_instructions) {
    my_instructions.addAll(the_instructions);
  }

  /**
   * Removes from the representation of the instructions the instructions
   * contained in the given region. The bounds of the region are included
   * in the removal operation. We assume that the <code>first</code> and
   * <code>the_last</code> are within the range of available line numbers.
   *
   * @param the_first the first line of the region
   * @param the_last the last line of the region
   */
  protected final void removeInstructionsInRegion(final int the_first,
                                                  final int the_last) {
    for (int i = the_first; i <= the_last; i++) {
      final BytecodeLineController blc = getLineController(i);
      my_instructions.remove(blc);
    }
  }

  /**
   * Insertst the given list of instructions at the given position. The
   * instructions after and including the postion <code>a_pos</code> are
   * shifted to the right (i.e. their indicies are increased) the number
   * of positions that is enough to cover the given list
   * <code>the_instructions</code>.
   *
   * @param a_pos the postion where the list is inserted
   * @param the_instructions the list to insert
   */
  protected final void insertInstructions(final int a_pos,
                                          final LinkedList the_instructions) {
    my_instructions.addAll(a_pos, the_instructions);
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
   * This is a helper method used for debugging purposes. It prints out
   * all the instructions in the internal Umbra representation of a class
   * file.
   *
   * @param an_index the number which allows to make different printouts
   */
  protected final void controlPrint(final int an_index) {
    UmbraPlugin.messagelog("");
    UmbraPlugin.messagelog("Control print of bytecode modification (" +
                           an_index + "):");
    for (int i = 0; i < my_instructions.size(); i++) {
      final InstructionLineController line =
                            (InstructionLineController)my_instructions.get(i);
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
}
