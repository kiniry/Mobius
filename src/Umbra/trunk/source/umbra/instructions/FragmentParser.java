/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;

import umbra.UmbraException;
import umbra.UmbraRuntimeException;
import umbra.editor.BytecodeDocument;
import umbra.editor.parsing.UmbraLocationException;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.UnknownLineController;

/**
 * This class is used to parse fragments of byte code textual documents.
 * Currently it handles only fragments included in a single method.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class FragmentParser extends BytecodeTextParser {

  /**
   * The document which contains the fragment to be parsed.
   */
  private BytecodeDocument my_doc;

  /**
   * The first line to be parsed. The parsing includes this line.
   */
  private int my_start;

  /**
   * The last line to be parsed. The parsing includes this line.
   */
  private int my_end;
  //@ invariant my_end < my_doc.getNumberOfLines();

  /**
   * The method number of the method in which the fragment is located.
   * We currently assume that all the modifications are included in a single
   * method.
   */
  private int my_methodno;
  //@ invariant my_methodno >= 0;

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
    super(null);
    my_doc = a_doc;
    my_start = the_firstline;
    my_end = the_lastline;
    my_methodno = a_methodno;
  }

  /**
   * Parsing of the current fragment of the document.
   * It uses BCEL objects associated with the
   * document and based on them it generates the Umbra line
   * structures (subclasses of the {@link BytecodeLineController})
   * together with the links to the BCEL objects.
   *
   * This method initialises the parsing context so that the parsing is
   * inside of a method, then it parses the lines in the related document
   * area.
   */
  public final void runParsing() {
    final LineContext ctxt = new LineContext();
    ctxt.seClassToBeRead();
    ctxt.setMethodNo(my_methodno);
    int a_line_no = my_start;
    try {
      a_line_no = swallowMethodBodyFragment(a_line_no, my_end, ctxt);
    } catch (UmbraLocationException e) {
      MessageDialog.openInformation(new Shell(), "Bytecode fragment parsing",
                      "The current document has no positions for a line " +
                      "after " + e.getWrongLocation());
    } catch (UmbraException e) {
      MessageDialog.openInformation(new Shell(), "Bytecode fragment parsing",
                         "The current document has too many methods (" +
                         my_methodno + ")");
    }
    if (a_line_no > my_end + 1)
      throw new UmbraRuntimeException();
  }

  /**
   * This method parses a fragment of a single method. The fragment is delimited
   * with {@code a_start} and {@code an_end} (inclusively). The line context
   * gives the number of the current method and should be set in the
   * state that corresponds to parsing of a method.
   *
   * @param a_start the first parsed line
   * @param an_end the last parsed line
   * @param a_ctxt the parsing context
   * @return the first line to be parsed by the further parsing procedure
   * @throws UmbraLocationException in case the method reaches a line number
   *   which is not within the given document
   * @throws UmbraException in case parsing reached an unexpected line
   */
  private int swallowMethodBodyFragment(final int a_start,
                                        final int an_end,
                                        final LineContext a_ctxt)
    throws UmbraLocationException, UmbraException {
    int j = a_start;
    for (; j <= an_end; j++) {
      final String lineName = getLineFromDoc(my_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(lineName,
                                                           a_ctxt);
      addEditorLine(lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      if (lc.isCommentStart()) { // ignore comments
        j = swallowComment(my_doc, j, an_end, a_ctxt);
        continue;
      }
      if (lc instanceof HeaderLineController) { // method header
        throw new UmbraException();
      }
      if (lc instanceof EmptyLineController) { //method end
        return swallowEmptyLines(my_doc, j, a_ctxt);
      }
      if (lc instanceof InstructionLineController) { //instruction line
        getInstructions().add(lc);
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
    while (j <= the_last_lno) {
      final String line = getLineFromDoc(a_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(line, a_ctxt);
      if (!(lc instanceof CommentLineController)) {
        break;
      }
      addEditorLine(j, lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      j++;
    }
    return j;
  }
}
