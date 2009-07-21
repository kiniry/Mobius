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

import org.apache.bcel.generic.MethodGen;

import annot.bcclass.BCMethod;

import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.lib.BytecodeStrings;
import umbra.lib.UmbraMethodException;

/**
 * This class handles the operations which are common to all the document
 * parsers that are used in Umbra.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public abstract class BytecodeTextParser {

  /**
   * The list of all the lines in the current byte code editor. These lines
   * are stored as objects the classes of which are subclasses of
   * {@link BytecodeLineController}.
   */
  private LinkedList my_editor_lines;

  /**
   * A temporary counter of instruction lines. It is used to synchronise the
   * currently parsed document with an old comments structure. This number
   * is a sequence number increased by one with each instruction (not the
   * byte code label number).
   */
  private int my_instruction_no;

  /**
   * The list of all the lines in the editor which contain codes of
   * instructions. These are represented as objects the classes of which
   * are subclasses of {@link InstructionLineController}.
   */
  private LinkedList my_instructions;

  /**
   * This constructor initialises internal structure to represent
   * editor lines and instructions.
   */
  protected BytecodeTextParser() {
    super();
    my_editor_lines = new LinkedList();
    my_instructions = new LinkedList();
  }

  /**
   * The method checks if the given line contains a single line comment
   * and extracts the comment string. In case there is no
   * comment in the line, it returns <code>null</code>.
   * In case the parsing context is such that we are inside a many-line
   * comment, then the comment inside a line is always empty.
   * Additionally, this method removes the end-of-line char from the
   * string.
   *
   * @param a_line_text the line to check for my_eolcomments
   * @param a_ctxt the parsing context for the line
   * @return comment or <code>null</code> in case there is no comment in the
   *         line
   */
  public static String extractCommentFromLine(final String a_line_text,
                                        final LineContext a_ctxt) {
    if (a_ctxt.isInsideComment()) return null;
    final InstructionParser parser = new InstructionParser(a_line_text);
    int posq = a_line_text.indexOf("\"");
    int posc = a_line_text.indexOf(BytecodeStrings.SINGLE_LINE_COMMENT_MARK);
    parser.moveIndex(posq + 1);
    while (0 <= posq && posq <= posc) {
      parser.swallowString();
      posq = a_line_text.indexOf("\"", parser.getIndex() + 1);
      posc = a_line_text.indexOf(BytecodeStrings.SINGLE_LINE_COMMENT_MARK,
                            parser.getIndex() + 1);
      parser.moveIndex(parser.getIndex() - posq - 1);
    }
    if (posc == -1) {
      return null;
    }
    String nl = a_line_text.substring(posc +
                                  BytecodeStrings.SINGLE_LINE_COMMENT_MARK_LEN,
                                  a_line_text.length());
    if (nl.indexOf('\n') >= 0)
      nl = nl.substring(0, nl.indexOf('\n'));
    return nl;
  }


  /**
   * This method retrieves from the given byte code document the BCEL structure
   * corresponding to the method of the given number. This method checks if
   * there are enough methods in the BCEL structure of the document and in
   * case there are not enough of them it throws an exception.
   *
   * @param a_doc a document to retrieve the BCEL structure of a method
   * @param a_method_no the method number of the method to retrieve the
   *    structure for
   * @return the BCEL structure which describes the method
   * @throws UmbraMethodException in case the given method number is wrong
   */
  protected static BCMethod getMethodGenFromDoc(final BytecodeDocument a_doc,
                                                final int a_method_no)
    throws UmbraMethodException {
    return a_doc.getMethodGen(a_method_no);
  }

  /**
   * Removes an one-line comment from a line of byte code.
   *
   * @param a_line a line of byte code
   * @param line_delimiter line delimiter for the line of bytecode
   * @return the byte code line without end-of-line comment and final
   *   whitespace
   */
  public static final String removeCommentFromLine(
      final String a_line, final String a_line_delimiter) {
    String res;
    final InstructionParser parser = new InstructionParser(a_line);
    int j = a_line.length() - 1;
    int posq = a_line.indexOf("\"");
    int posc = a_line.indexOf(BytecodeStrings.SINGLE_LINE_COMMENT_MARK);
    parser.moveIndex(posq + 1);
    while (0 <= posq && posq <= posc) {
      parser.swallowString();
      posq = a_line.indexOf("\"", parser.getIndex() + 1);
      posc = a_line.indexOf(BytecodeStrings.SINGLE_LINE_COMMENT_MARK,
                            parser.getIndex() + 1);
      parser.moveIndex(parser.getIndex() - posq - 1);
    }
    if (posc != -1)
      j = posc - 1;
    while ((j >= 0) && (Character.isWhitespace(a_line.charAt(j))))
      j--;
    res = a_line.substring(0, j + 1);
    if (a_line_delimiter != null && a_line.endsWith(a_line_delimiter))
      res += a_line_delimiter;
    return res;
  }

  /**
   * Returns the list of all the lines in the internal representation.
   * This method may only be called once to export fully generated
   * list of lines.
   *
   * @return the list of the {@link BytecodeLineController} objects that
   *   represent all the lines in the currently parsed document
   */
  public LinkedList getEditorLines() {
    final LinkedList lines = my_editor_lines;
    my_editor_lines = null;
    return lines;
  }

  /**
   * Returns the list of all the lines in the internal representation.
   *
   * @return the list of the {@link BytecodeLineController} objects that
   *   represent all the lines in the currently parsed document
   */
  public LinkedList getEditorLinesPreserve() {
    return my_editor_lines;
  }

  /**
   * This method adds the specified line controller at the specified position.
   * It shifts the element currently at that position (if any) and any
   * subsequent elements to the right (adds one to their indices).
   *
   * @param a_pos the position in the document where to insert the line
   * @param a_line the line to be inserted
   */
  public void addEditorLine(final int a_pos,
                            final BytecodeLineController a_line) {
    final int pos_in_combined = getPosOfLine(a_pos);
    String instr = a_line.getLineContent();
    insertAt(pos_in_combined, instr);
    enrichWithComment(a_line, pos_in_combined, my_instruction_no);
    my_editor_lines.add(a_pos, a_line);
  }

  //@ requires a_lineno >= 0;
  /**
   * Returns the position of the first character in the line of the given
   * number.
   *
   * @param a_lineno the number of the line to find the position for
   * @return the position of the first character in the line
   */
  protected abstract int getPosOfLine(final int a_lineno);

  /**
   * Inserts the given string in the current representation of the combined
   * text (class+comments) at the indicated position.
   *
   * @param a_pos the position to insert the string at
   * @param a_string the string to insert
   */
  protected abstract void insertAt(int a_pos, String a_string);

  /**
   * This method adds to the combination of the currently parsed text and the
   * information from the comment structures the comment associated with the
   * given line.
   *
   * If the given line controller is not an {@link InstructionLineController}
   * then the method does nothing.
   *
   * @param a_line a line controller to associate comments with
   * @param a_pos the position in the combined text where the comment
   *   is to be added
   * @param a_instno the number of a instruction with which the comment
   *   should be associated
   */
  protected abstract void enrichWithComment(final BytecodeLineController a_line,
                                            final int a_pos,
                                            final int a_instno);

  /**
   * This method adds to the combination of the currently parsed text and the
   * information from the comment structures the text of the given instruction
   * together with the comment associated with the line. We assume that the text
   * of the line controller is not already in the combined text string.
   * If the given line controller is not an {@link InstructionLineController}
   * then the method only appends the content of the given line controller
   *
   * @param a_line a line controller to associate comments with
   * @param a_instno the number of a instruction with which the comment
   *   should be associated
   */
  protected abstract void enrichWithComment(
     final BytecodeLineController a_line,
     final int a_instno);

  /**
   * This method appends the specified line cotroller at the end of the lines
   * structure.
   *
   * @param a_line the line to be inserted
   */
  public void addEditorLine(final BytecodeLineController a_line) {
    my_editor_lines.add(a_line);
    enrichWithComment(a_line, my_instruction_no);
  }

  /**
   * Returns the list of all the lines with instructions in the internal
   * representation. This method may only be called once to export fully
   * generate list of lines.
   *
   * @return the list of the {@link BytecodeLineController} objects that
   *   represent the lines with instructions in the currently parsed document
   */
  public LinkedList getInstructions() {
    final LinkedList lines = my_instructions;
    my_instructions = null;
    return lines;
  }

  /**
   * Adds the given instruction line controller to the collection of the
   * instruction lines. Additionally, this method handles the adding of the
   * comments from the currently parsed document to the structures which
   * represent the comments internally. It is done here as all the
   * comments are associated with the instruction lines.
   *
   * @param a_lc the line controller to add
   * @return the number of the currently added instruction
   */
  protected int addInstruction(final InstructionLineController a_lc) {
    adjustCommentsForInstruction(a_lc, my_instruction_no);
    my_instructions.add(a_lc);
    return my_instruction_no;
  }

  /**
   * The method updates the comments structures.
   *
   * @param a_lc the line controller to associate the comments with
   * @param an_instrno the instruction number of the given controller
   */
  protected abstract void adjustCommentsForInstruction(
                               final InstructionLineController a_lc,
                               final int an_instrno);

  /**
   * Increases by one the current instruction number.
   */
  protected void incInstructionNo() {
    my_instruction_no++;
  }

  /**
   * Initialises the instruction counter to the first value.
   */
  protected void initInstructionNo() {
    my_instruction_no = 0;
  }

  /**
   * Assigns the method number included in the given line context to the
   * annotation lines block at the end of the current collection of the
   * editor lines.
   *
   * @param a_ctxt a context with the method number to assign
   */
  protected void updateAnnotations(final LineContext a_ctxt) {
    for (int i = my_editor_lines.size() - 1; i >= 0; i--) {
      final BytecodeLineController blc =
        (BytecodeLineController)my_editor_lines.get(i);
      if (blc instanceof AnnotationLineController) {
        final AnnotationLineController alc = (AnnotationLineController) blc;
        alc.setMethodNo(a_ctxt.getMethodNo());
      } else {
        return;
      }
    }
  }

  /**
   * Converts the given line number to the corresponding instruction number.
   * This method returns the instruction number only for lines that contain
   * instructions. For other lines the method returns -1.
   *
   * @param a_lineno the line number for which the instruction number is
   *   retrieved
   * @return the number of instruction or -1 in case the given line number
   *   does not contain an instruction
   */
  protected int getInstructionNoForLine(final int a_lineno) {
    if (my_instructions == null || my_editor_lines.size() <= a_lineno)
      return -1;
    final BytecodeLineController blc =
                   (BytecodeLineController) my_editor_lines.get(a_lineno);
    for (int i = 0; i < my_instructions.size(); i++) {
      if (blc == my_instructions.get(i)) {
        return i;
      }
    }
    return -1;
  }
}
