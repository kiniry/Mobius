/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.Hashtable;
import java.util.LinkedList;

import org.apache.bcel.generic.MethodGen;
import org.eclipse.jface.text.BadLocationException;

import umbra.editor.BytecodeDocument;
import umbra.editor.UmbraMethodException;
import umbra.editor.parsing.BytecodeStrings;
import umbra.editor.parsing.UmbraLocationException;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.InstructionLineController;

/**
 * This class handles the operations which are common to all the document
 * parsers that are used in Umbra.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class BytecodeTextParser {


  /**
   * This field contains the texts of end-of-line comments which were introduced
   * in the previous session with, the current document. The i-th entry contains
   * the comment for the i-th instruction in the document, if this array
   * is null then the array is not taken into account.
   */
  private String[] my_eolcomment_array;

  /**
   * This field contains the texts of interline comments which were introduced
   * in the previous session with, the current document. The i-th entry contains
   * the comment for the i-th instruction in the document, if this array
   * is null then the array is not taken into account.
   */
  private String[] my_interline_array;

  /**
   * The container of associations between the Umbra representation of lines
   * in the byte code editor and the end-of-line comments in these lines.
   * The comments must be absent from the line representation for their
   * correct parsing so they are held in this additional structure.
   */
  private Hashtable my_eolcomments;

  /**
   * The container of associations between the Umbra representation of lines
   * in the byte code editor and the multi-line comments in these lines.
   * The comments must be absent from the line representation for their
   * correct parsing so they are held in this additional structure.
   * FIXME: this is not handled properly
   */
  private Hashtable my_interline_comments;

  /**
   * This field contains the value of the end-of-line comment from the currently
   * parsed line.
   */
  private String my_current_comment;

  /**
   * This field contains the value of the interline comment from the currently
   * parsed code fragment.
   */
  private StringBuffer my_current_icomment;

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

  private StringBuffer my_combined_text;

  /**
   * This constructor initialises internal structure to represent
   * editor lines, instructions, and comments. The given parameter is the
   * value of the array which contains the comments from the previous session
   * with the current document.
   *
   * TODO link to the protocol for a_comment_array
   * @param a_comment_array the end-of-line comments from the previous session
   * @param a_interline the interline comments from the previous session
   */
  protected BytecodeTextParser(final String[] a_comment_array,
                               final String[] a_interline) {
    super();
    my_editor_lines = new LinkedList();
    my_instructions = new LinkedList();
    my_eolcomment_array = a_comment_array;
    my_interline_array = a_interline;
    my_eolcomments = new Hashtable();
    my_interline_comments = new Hashtable();
    my_combined_text = new StringBuffer("");
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
    final int i = a_line_text.indexOf(BytecodeStrings.SINGLE_LINE_COMMENT_MARK);
    if (i == -1) {
      return null;
    }
    String nl = a_line_text.substring(i +
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
  protected static MethodGen getMethodGenFromDoc(final BytecodeDocument a_doc,
                                                 final int a_method_no)
    throws UmbraMethodException {
    return a_doc.getMethodGen(a_method_no);
  }

  /**
   * Removes an one-line comment from a line of byte code.
   *
   * @param a_line a line of byte code
   * @return the byte code line without end-of-line comment and final
   *   whitespace
   */
  public static final String removeCommentFromLine(final String a_line) {
    String res;
    int j = a_line.length() - 1;

    final int k = (a_line.indexOf(BytecodeStrings.SINGLE_LINE_COMMENT_MARK, 0));
    if (k != -1)
      j = k - 1;
    while ((j >= 0) && (Character.isWhitespace(a_line.charAt(j))))
      j--;
    res = a_line.substring(0, j + 1) + "\n";
    return res;
  }

  /**
   * Returns the association between the lines in the internal Umbra
   * representation and the end-of-line comments present in the textual
   * representation.
   *
   * @return the list of the {@link BytecodeLineController} objects that
   *   represent the lines with instructions in the currently parsed document
   */
  public Hashtable getComments() {
    return my_eolcomments;
  }

  /**
   * Returns the association between the lines in the internal Umbra
   * representation and the multi-line comments present in the textual
   * representation.
   *
   * @return the list of the {@link BytecodeLineController} objects that
   *   represent the lines with instructions in the currently parsed document
   */
  public Hashtable getInterlineComments() {
    return my_interline_comments;
  }

  /**
   * @return the value of the current comment
   */
  public String getCurrentComment() {
    return my_current_comment;
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
   * This method adds the specified line controller at the specified position.
   * It shifts the element currently at that position (if any) and any
   * subsequent elements to the right (adds one to their indices).
   *
   * @param a_pos the position to insert the line
   * @param a_line the line to be inserted
   */
  public void addEditorLine(final int a_pos,
                            final BytecodeLineController a_line) {
    int pos_in_combined = getPosOfLine(a_pos);
    String instr = a_line.getLineContent();
    insertAfter(pos_in_combined, instr);
    if (a_line instanceof InstructionLineController &&
        my_current_comment != null) {
      String comm = "//" + my_current_comment;
      pos_in_combined += instr.length();
      insertAfter(pos_in_combined, comm);
      pos_in_combined += comm.length();
    }
    my_editor_lines.add(a_pos, a_line);
  }

  private void insertAfter(int pos_in_combined, String instr) {
    if (pos_in_combined == my_combined_text.length())
      my_combined_text.append(instr);
    else
      my_combined_text.insert(pos_in_combined + 1, instr);
  }

  private int getPosOfLine(int a_pos) {
    int start = -1;
    for (int i = 0; i < a_pos; i++) {
      start = my_combined_text.indexOf("\n", start + 1);
      if (start == -1) {
        return -1;
      }
    }
    return start;
  }

  /**
   * This method appends the specified line cotroller at the end of the lines
   * structure.
   *
   * @param a_line the line to be inserted
   */
  public void addEditorLine(final BytecodeLineController a_line) {
    my_editor_lines.add(a_line);
    my_combined_text.append(a_line.getLineContent());
    if (a_line instanceof InstructionLineController &&
        my_current_comment != null) {
      my_combined_text.append("//" + my_current_comment);
    }
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
   * This also handles the comments TODO
   * @param lc
   */
  protected void addInstruction(InstructionLineController lc) {
    if (my_eolcomment_array != null && my_current_comment == null) {
      my_current_comment = my_eolcomment_array[my_instruction_no];
    }
    if (my_interline_array != null && my_current_icomment == null &&
        my_interline_array[my_instruction_no] != null) {
      my_current_icomment = new StringBuffer(
                                     my_interline_array[my_instruction_no]);
    }
    if (my_current_icomment != null) {
      my_interline_comments.put(lc, my_current_icomment.toString());
    }
    my_current_icomment = null;
    if (my_current_comment != null)
      my_eolcomments.put(lc, my_current_comment);
    my_current_comment = null;
    my_instructions.add(lc);
  }

  /**
   * This method returns the {@link String} with the given line of the given
   * document. Additionally, the method extracts the end-of-line comment and
   * stores it in the internal state of the current object. The method needs
   * the parsing context in case the line is a part of a multi-line context.
   * In that case, the end-of-line comment should not be extracted.
   *
   * @param a_doc a document to extract the line from
   * @param a_line the line number of the line to be extracted
   * @param a_ctxt a context which indicates if we are inside a comment
   * @return the string with the line content (with the end-of-line comment
   *   stripped off)
   * @throws UmbraLocationException in case the given line number is not within
   *   the given document
   */
  protected String getLineFromDoc(final BytecodeDocument a_doc,
                                  final int a_line,
                                  final LineContext a_ctxt)
    throws UmbraLocationException {
    String line;
    try {
      line = a_doc.get(a_doc.getLineOffset(a_line),
                                    a_doc.getLineLength(a_line));
    } catch (BadLocationException e) {
      throw new UmbraLocationException(a_line);
    }
    final String lineName;
    if (!a_ctxt.isInsideComment() || !a_ctxt.isInsideAnnotation()) {
      lineName = removeCommentFromLine(line);
      my_current_comment = extractCommentFromLine(line, a_ctxt);
    } else {
      lineName = line;
      my_current_comment = null;
    }
    return lineName;
  }


  /**
   * This method stores in the local comments structure the information about
   * the currently extracted comment. It also handles the enriching of the
   * comments in the current version of the document with the information
   * from the previous one the content of which was refreshed.
   *
   * @param a_lc the line controller to associate the comment to
   */
  protected void handleComments(final BytecodeLineController a_lc) {
    if (my_current_comment != null) {
      my_eolcomments.put(a_lc, my_current_comment);
      my_current_comment = null;
    }
    if (my_eolcomment_array != null) {
      if (my_eolcomment_array[my_instruction_no] != null) {
        if (my_eolcomments.contains(a_lc)) my_eolcomments.remove(a_lc);
        my_eolcomments.put(a_lc, my_eolcomment_array[my_instruction_no]);
      }
    }
  }

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
   * This method sets the value of the end-of-line comment from the currently
   * parsed line.
   *
   * @param a_comment the current comment value to set
   */
  public void setCurrentComment(final String a_comment) {
    my_current_comment = a_comment;
  }

  /**
   * This method parses from the given document lines which are considered
   * to be empty lines in the given context. A line is empty when it
   * contains white spaces only or is one of the possible kinds of
   * comment lines. The parsing stops at the first line which cannot
   * be considered empty. This line will be parsed once more by the subsequent
   * parsing procedure. We ensure here that the {@link AnnotationLineController}
   * has the method number of either the current method or the method right
   * after the annotation.
   *
   * @param a_doc a document to extract empty lines from
   * @param the_current_lno the first line to be analysed
   * @param a_ctxt a parsing context in which the document is analysed
   * @return the first line which is not an empty line; in case the end
   *   of the document is reached this is the number of lines in the
   *   document
   * @throws UmbraLocationException in case the method reaches a line number
   *   which is not within the given document
   */
  protected int swallowEmptyLines(final BytecodeDocument a_doc,
                                  final int the_current_lno,
                                  final LineContext a_ctxt)
    throws UmbraLocationException {
    int j = the_current_lno;
    while (j < a_doc.getNumberOfLines()) {
      final String line = getLineFromDoc(a_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(line, a_ctxt);
      if (!(lc instanceof CommentLineController)  &&
          !(lc instanceof EmptyLineController)) {
        break;
      }
      if (lc instanceof AnnotationLineController)
        ((AnnotationLineController)lc).setMethodNo(a_ctxt.getMethodNo());
      addEditorLine(lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      j++;
    }
    return j;
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

  protected void markReadyToConsumeComments() {
    // TODO Auto-generated method stub
    
  }
  
  protected void clearCurrentComment() {
    my_current_icomment = new StringBuffer("");
  }
  
  protected void addToCurrentComment(String line) {
   my_current_icomment.append(line); 
  }
  
  private void commitCurrentComment() {
    // TODO Auto-generated method stub
    
  }

  protected String getNewContent() {
    return my_combined_text.toString();
  }

}
