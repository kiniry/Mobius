/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.FieldLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.UnknownLineController;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraException;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraRuntimeException;

/**
 * This class is used to parse fragments of byte code textual documents.
 * Currently it handles only fragments included in a single method.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class FragmentParser extends BytecodeCommentParser {

  /**
   * The document which contains the fragment to be parsed.
   */
  private final BytecodeDocument my_doc;

  /**
   * The first line to be parsed. The parsing includes this line.
   */
  private final int my_start;

  /**
   * The last line to be parsed. The parsing includes this line.
   */
  private final int my_end;
  //@ invariant my_end < my_doc.getNumberOfLines();

  /**
   * This constructor creates the fragment parser for the given fragment.
   * The parser will parse the content of {@code a_doc} parameter within the
   * range starting with the line {@code the_firstline} and ending
   * with the line {@code the_lastline}. All the lines in the range including
   * its borders are parsed. Additionally, we assume the lines are within a
   * single method. The method number (as counted in the document) is
   * given and is used to initialise some of the data structures. At last the
   * array with comment lines from the previous session is given.
   *
   * @param a_doc a document to be parsed
   * @param the_firstline the first line to be parsed
   * @param the_lastline the last line to be parsed
   * @param a_methodno the number of the method within which the changes are
   *   located
   */
  public FragmentParser(final BytecodeDocument a_doc,
                        final int the_firstline,
                        final int the_lastline,
                        final int a_methodno) {
    super(null, null);
    my_doc = a_doc;
    my_start = the_firstline;
    my_end = the_lastline;
  }

  /**
   * Parsing of the current fragment of the document.
   * It uses BCEL objects associated with the
   * document and based on them it generates the Umbra line
   * structures (subclasses of the {@link BytecodeLineController})
   * together with the links to the BCEL objects. It checks if the
   * edit operation is appropriate. Currently, it means that the
   * operation does not cross or destroy the boundaries of the existing
   * regions.
   *
   * This method initialises the parsing context so that the parsing is
   * inside of a method, then it parses the lines in the related document
   * area.
   *
   * @param a_ctxt the parsing context for the given fragment
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   */
  public final void runParsing(final LineContext a_ctxt)
    throws UmbraLocationException {
    int a_line_no = my_start;
    try {
      if (a_ctxt.isInsideConstantPool()) {
        a_line_no = swallowCPFragment(a_line_no, a_ctxt);
      } else if (a_ctxt.isInsideAnnotation()) {
        a_line_no = swallowAnnotationFragment(a_line_no, a_ctxt);
      } else if (a_ctxt.isInsideMethod()) {
        a_line_no = swallowMethodBodyFragment(a_line_no, a_ctxt);
      } else if (a_ctxt.isInInvariantArea()) {
        a_line_no = swallowEmptyLines(my_doc, a_line_no, my_end, a_ctxt);
        if (a_line_no <= my_end) {
          a_line_no = swallowAnnotationFragment(a_line_no, a_ctxt);
          //a_line_no = swallowEmptyLines(my_doc, a_line_no, my_end, a_ctxt);
        }
      } else if (a_ctxt.isInFieldsArea()) {
        a_line_no = swallowEmptyLines(my_doc, a_line_no, my_end, a_ctxt);
        if (a_line_no <= my_end) {
          a_line_no = swallowFields(a_line_no, my_end, a_ctxt);
        }
      } else {
        throw new UmbraException();
      }
    } catch (UmbraException e) {
      GUIMessages.messageWrongLocation(my_doc.getEditor().getSite().getShell(),
        GUIMessages.FRAGMENT_PARSING_MESSAGE_TITLE,
        new UmbraLocationException(true, a_line_no, true));
    }
    if (a_line_no > my_end + 1)
      throw new UmbraRuntimeException("Too high line number: " + a_line_no);
  }

  /**
   * @param the_current_lno the first line to be parsed
   * @param the_last_lno the last line to be parsed
   * @param a_ctxt the parsing context
   * @return the first line to be parsed by the further parsing procedure
   * @throws UmbraLocationException in case the method reaches a line number
   *   which is not within the given document
   */
  private int swallowFields(final int the_current_lno,
                            final int the_last_lno,
                            final LineContext a_ctxt)
    throws UmbraLocationException {
    int j = the_current_lno;
    while (j <= the_last_lno) {
      final String line = getLineFromDoc(my_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(line, a_ctxt,
                                                           my_doc.getBmlp());
      if (!(lc instanceof FieldLineController) &&
          !(lc instanceof EmptyLineController)) {
        break;
      }
      addEditorLine(lc);
      j++;
    }
    return j;
  }

  /**
   * This method parses a fragment of a constant pool. The fragment is delimited
   * with {@code a_start} and {@code my_end} (inclusively). The line context
   * gives the number of the current method and should be set in the
   * state that corresponds to parsing of a constant pool.
   *
   * @param a_start the first parsed line
   * @param a_ctxt the parsing context
   * @return the first line to be parsed by the further parsing procedure
   * @throws UmbraLocationException in case the method reaches a line number
   *   which is not within the given document
   */
  private int swallowCPFragment(final int a_start, final LineContext a_ctxt)
    throws UmbraLocationException {
    int j = a_start;
    while (j <= my_end) {
      final String line = this.getLineFromDoc(my_doc, j, a_ctxt);
      final BytecodeLineController blc =
        Preparsing.getType(line, a_ctxt, my_doc.getBmlp());
      addEditorLine(blc);
      j++;
    }
    return my_end;
  }

  /**
   * This method parses a fragment of an annotation. The fragment is delimited
   * with {@code a_start} and {@code my_end} (inclusively). The line context
   * gives the number of the current method and should be set in the
   * state that corresponds to parsing of a method.
   *
   * @param a_start the first parsed line
   * @param a_ctxt the parsing context
   * @return the first line to be parsed by the further parsing procedure
   * @throws UmbraLocationException in case the method reaches a line number
   *   which is not within the given document
   * @throws UmbraException in case parsing reached a boundary of the
   *   recognised regions
   */
  private int swallowAnnotationFragment(final int a_start,
                                        final LineContext a_ctxt)
    throws UmbraLocationException, UmbraException {
    int j = a_start;
    BytecodeLineController lc = null;
    for (; j <= my_end; j++) {
      final String lineName = getLineFromDoc(my_doc, j, a_ctxt);
      lc = Preparsing.getType(lineName, a_ctxt, my_doc.getBmlp());
      addEditorLine(lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      if (!(lc instanceof CommentLineController) &&
          !(lc instanceof UnknownLineController) &&
          !(lc instanceof EmptyLineController)) { //we allow only unknown,
                                                  //empty & annotation lines
        throw new UmbraException();
      }
    }
    return j;
  }

  /**
   * This method parses a fragment of a single method. The fragment is delimited
   * with {@code a_start} and {@code an_end} (inclusively). The line context
   * gives the number of the current method and should be set in the
   * state that corresponds to parsing of a method.
   *
   * @param a_start the first parsed line
   * @param a_ctxt the parsing context
   * @return the first line to be parsed by the further parsing procedure
   * @throws UmbraLocationException in case the method reaches a line number
   *   which is not within the given document
   * @throws UmbraException in case parsing reached an unexpected line
   */
  private int swallowMethodBodyFragment(final int a_start,
                                        final LineContext a_ctxt)
    throws UmbraLocationException, UmbraException {
    int j = a_start;
    for (; j <= my_end; j++) {
      final String lineName = getLineFromDoc(my_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(lineName,
                                                           a_ctxt,
                                                           my_doc.getBmlp());
      addEditorLine(lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      if (lc.isCommentStart()) { // process comments
        j = swallowComment(my_doc, j + 1, my_end, a_ctxt) - 1;
        continue;
      }
      if (lc instanceof HeaderLineController) { // method header
        throw new UmbraException();
      }
      if (lc instanceof EmptyLineController) { //method end
        return swallowEmptyLines(my_doc, j, my_end, a_ctxt);
      }
      if (lc instanceof InstructionLineController) { //instruction line
        addInstruction((InstructionLineController)lc);
      } else if (!(lc instanceof UnknownLineController)) { //we allow unknown
        throw new UmbraException();
      }
    }
    return j;

  }

  /**
   * This method parses from the given document lines which are considered
   * to be comment lines in the given context. The parsing stops at the first
   * line which cannot be considered a comment line. This line will be parsed
   * once more by the subsequent parsing procedure.
   *
   * @param a_doc a document to extract comment lines from
   * @param the_current_lno the first line to be analysed
   * @param the_last_lno the last line to be analysed
   * @param a_ctxt a parsing context in which the document is analysed
   * @return the first line which is not a comment line; in case the last
   *   line is reached this is the number of the last line plus 1
   *
   * @throws UmbraLocationException in case the method reaches a line number
   *   which is not within the given document
   */
  private int swallowComment(final BytecodeDocument a_doc,
                                final int the_current_lno,
                                final int the_last_lno,
                                final LineContext a_ctxt)
    throws UmbraLocationException {
    int j = the_current_lno;
    clearCurrentComment();
    while (j <= the_last_lno) {
      final String line = getLineFromDoc(a_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(line, a_ctxt,
                                                           my_doc.getBmlp());
      if (!(lc instanceof CommentLineController)) {
        break;
      }
      addEditorLine(lc);
      addToCurrentComment(line);
      lc.setMethodNo(a_ctxt.getMethodNo());
      j++;
    }
    return j;
  }


}
