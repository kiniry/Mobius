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

import org.eclipse.jface.text.BadLocationException;

import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.lib.BytecodeStrings;
import umbra.lib.UmbraLocationException;

/**
 * This class handles the operations which are connected with the handling of
 * the comments.
 *
 * FIXME: this is the best place to describe the logics of the comment saving
 *   https://mobius.ucd.ie/ticket/560
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class BytecodeCommentParser extends BytecodeTextParser {


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
   * FIXME: this is not handled properly; https://mobius.ucd.ie/ticket/555
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
   * The combination of the currently parsed text and the information from
   * the comment structures. The process of parsing results in a combined
   * version which includes both the original text and the textual
   * representation of comments.
   */
  private StringBuffer my_combined_text;

  /**
   * This constructor initialises internal structure to represent
   * comments. The given parameters are the
   * value of the arrays which contain the comments from the previous session
   * with the current document.
   *
   * FIXME link to the protocol for a_comment_array;
   *   https://mobius.ucd.ie/ticket/560
   *
   * @param a_comment_array the end-of-line comments from the previous session
   * @param a_interline the interline comments from the previous session
   */
  protected BytecodeCommentParser(final String[] a_comment_array,
                                  final String[] a_interline) {
    super();
    my_eolcomment_array = a_comment_array;
    my_interline_array = a_interline;
    my_eolcomments = new Hashtable();
    my_interline_comments = new Hashtable();
    my_combined_text = new StringBuffer("");
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
    final String line;
    final String line_delimiter;
    try {
      line = a_doc.get(a_doc.getLineOffset(a_line),
                                    a_doc.getLineLength(a_line));
      line_delimiter = a_doc.getLineDelimiter(a_line);
    } catch (BadLocationException e) {
      throw new UmbraLocationException(a_line, true);
    }
    final String lineName;
    if (!a_ctxt.isInsideComment() || !a_ctxt.isInsideAnnotation()) {
      lineName = removeCommentFromLine(line, line_delimiter);
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
   * @param an_instrno the number of the instruction to be added
   */
  protected void handleComments(final BytecodeLineController a_lc,
                                final int an_instrno) {
    if (my_current_comment != null) {
      my_eolcomments.put(a_lc, my_current_comment);
      my_current_comment = null;
    }
    if (my_eolcomment_array != null) {
      if (my_eolcomment_array[an_instrno] != null) {
        if (my_eolcomments.contains(a_lc)) my_eolcomments.remove(a_lc);
        my_eolcomments.put(a_lc, my_eolcomment_array[an_instrno]);
      }
    }
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
   * @param the_last_lno the line after which the document should not be
   *   analysed
   * @param a_ctxt a parsing context in which the document is analysed
   * @return the first line which is not an empty line; in case the end
   *   of the document is reached this is the number of lines in the
   *   document
   * @throws UmbraLocationException in case the method reaches a line number
   *   which is not within the given document
   */
  protected int swallowEmptyLines(final BytecodeDocument a_doc,
                                  final int the_current_lno,
                                  final int the_last_lno,
                                  final LineContext a_ctxt)
    throws UmbraLocationException {
    int j = the_current_lno;
    while (j <= the_last_lno) {
      final String line = getLineFromDoc(a_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(line, a_ctxt,
                                                           a_doc.getBmlp());
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
   * Clears the current representation of the multi-line comment.
   */
  protected void clearCurrentComment() {
    my_current_icomment = new StringBuffer("");
  }

  /**
   * Appends the given string at the end of the current multi-line comment.
   *
   * @param a_line the string to append
   */
  protected void addToCurrentComment(final String a_line) {
    my_current_icomment.append(a_line);
  }

  /**
   * This method adds to the combination of the currently parsed text and the
   * information from the comment structures the comment associated with the
   * given line. The method checks if the given line controller is an
   * instruction line controller and in that case it retrieves the comment
   * for the currently parsed line and inserts in the combined text after the
   * text of the current instruction. We assume that the text of the instruction
   * is already in the combined text string.
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
  protected final void enrichWithComment(final BytecodeLineController a_line,
                                         final int a_pos,
                                         final int a_instno) {
    int pos = a_pos;
    final String commi = getCommentForInstr(a_instno);
    if (a_line instanceof InstructionLineController &&
        commi != null) {
      final String instr = a_line.getLineContent();
      final String comm = " " + BytecodeStrings.SINGLE_LINE_COMMENT_MARK +
                          commi;
      pos += instr.length() - 1; // -1 for eol
      insertAt(pos, comm);
      pos += comm.length();
    }
  }

  /**
   * Retrieves the comment associated with the given instruction number. It
   * checks if a comment is associated with the currently parsed line. In that
   * case this comment is returned. In case there is no comment in the parsed
   * text, the structure of the comments from the previous session
   * {@link #my_eolcomment_array} is consulted.
   *
   * @param a_instno the instruction number with which the comment is associated
   * @return the string of the comment or <code>null</code> in case there is
   *   no comment
   */
  private String getCommentForInstr(final int a_instno) {
    String commi = null;
    if (my_current_comment != null) {
      commi = my_current_comment;
    } else if (my_eolcomment_array != null &&
               my_eolcomment_array.length > a_instno) {
      commi = my_eolcomment_array[a_instno];
    }
    return commi;
  }

  /**
   * This method adds to the combination of the currently parsed text and the
   * information from the comment structures the text of the given instruction
   * together with the comment associated with the line. The method adds always
   * the content of the line controller string and  if the given line
   * controller is an instruction line controller it retrieves the comment
   * for the currently parsed line and inserts in the combined text after the
   * text of the current instruction. We assume that the text of the line
   * controller is not already in the combined text string.
   *
   * If the given line controller is not an {@link InstructionLineController}
   * then the method only appends the content of the given line controller
   *
   * @param a_line a line controller to associate comments with
   * @param a_instno the number of a instruction with which the comment
   *   should be associated
   */
  protected void enrichWithComment(final BytecodeLineController a_line,
                                   final int a_instno) {
    my_combined_text.append(a_line.getLineContent());
    final String commi = getCommentForInstr(a_instno);
    if (a_line instanceof InstructionLineController &&
        commi != null) {
      insertAt(my_combined_text.length() - 1,
               BytecodeStrings.SINGLE_LINE_COMMENT_MARK + commi);
    }
  }

  /**
   * Inserts the given string in the current representation of the combined
   * text (class+comments) at the indicated position. The first character of
   * the given string becomes the character at the given position and all the
   * further characters follow. The characters of the original document
   * starting at the given position are moved so that they start right after
   * the inserted text.
   *
   * @param a_pos the position to insert the string at
   * @param a_string the string to insert
   */
  protected void insertAt(final int a_pos, final String a_string) {
    if (a_pos >= my_combined_text.length())
      my_combined_text.append(a_string);
    else
      my_combined_text.insert(a_pos, a_string);
  }

  //@ requires a_lineno >= 0;
  /**
   * Returns the position of the first character in the line of the given
   * number.
   *
   * @param a_lineno the number of the line to find the position for (the
   *   numbers start with 0)
   * @return the position of the first character in the line
   */
  protected final int getPosOfLine(final int a_lineno) {
    int start = 0;
    for (int i = 0; i < a_lineno; i++) {
      start = my_combined_text.indexOf("\n", start + 1);
      if (start == -1) {
        return -1;
      }
    }
    return start + 1;
  }

  /**
   * Returns the current content of the string which contains the text of the
   * class file combined with the comments.
   *
   * @return the class text with comments
   */
  protected String getNewContent() {
    return my_combined_text.toString();
  }

  /**
   * The method updates the comments structures. It checks if the current
   * end-of-line comment and interline comments can be filled in with the
   * values of the comments from the previous session and adds the association
   * between the given line controller and the current comments.
   *
   * @param a_lc the line controller to associate the comments with
   * @param an_instrno the instruction number of the given controller
   */
  protected void adjustCommentsForInstruction(
                                final InstructionLineController a_lc,
                                final int an_instrno) {
    if (my_eolcomment_array != null && my_current_comment == null) {
      my_current_comment = my_eolcomment_array[an_instrno];
    }
    if (my_interline_array != null && my_current_icomment == null &&
        my_interline_array[an_instrno] != null) {
      my_current_icomment = new StringBuffer(
                                     my_interline_array[an_instrno]);
    }
    if (my_current_icomment != null) {
      my_interline_comments.put(a_lc, my_current_icomment.toString());
    }
    my_current_icomment = null;
    if (my_current_comment != null)
      my_eolcomments.put(a_lc, my_current_comment);
    my_current_comment = null;
  }

}
