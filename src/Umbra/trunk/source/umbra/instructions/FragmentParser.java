/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.Iterator;

import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Shell;

import umbra.UmbraException;
import umbra.UmbraRuntimeException;
import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;

/**
 * This class is used to parse fragments of byte code textual documents.
 * Currently it handles only fragments included in a single method.
 *
 * @author alx
 * @version a-01
 *
 */
public class FragmentParser extends BytecodeTextParser {


  private BytecodeDocument my_doc;
  private int my_start;
  private int my_end;
  //@ invariant my_end < my_doc.getNumberOfLines();
  private int my_methodno;
  //@ invariant my_methodno >= 0;

  /**
   * @param methodno 
   * 
   *
   */
  public FragmentParser(final BytecodeDocument a_doc,
                        final int a_start_rem, final int a_stop,
                        int methodno, String[] a_comment_array) {
    super(a_comment_array);
    my_doc = a_doc;
    my_start = a_start_rem;
    my_end = a_stop;
    my_methodno = methodno;
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
    while (a_line_no <= my_end) {
      try {
        a_line_no = swallowMethodBodyFragment(a_line_no, my_end,
                                              my_methodno, ctxt);
      } catch (BadLocationException e) {
        MessageDialog.openInformation(new Shell(), "Bytecode",
                      "The current document has no positions for line " +
                      a_line_no);
        break;
      } catch (UmbraException e) {
        MessageDialog.openInformation(new Shell(), "Bytecode",
                      "The current document has too many methods (" +
                      my_methodno + ")");
        break;
      }
    }
  }

  private int swallowMethodBodyFragment(int a_start, int an_end,
                                        int a_methodno,
                                        LineContext a_ctxt)
    throws BadLocationException, UmbraException {
    final MethodGen mg = BytecodeTextParser.getMethodGenFromDoc(my_doc,
      a_methodno);
    final InstructionList il = mg.getInstructionList();
    il.setPositions();
    final Iterator iter = il.iterator();
    int j = an_end;
    for (; j <= an_end; j++) {
      final String lineName = getLineFromDoc(my_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(lineName,
                                                           a_ctxt);
      getEditorLines().add(j, lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      if (lc.isCommentStart()) { // ignore comments
        j = swallowComment(my_doc, j, an_end, a_ctxt);
        continue;
      }
      if (lc instanceof HeaderLineController) { // method header
        throw new UmbraRuntimeException();
      }
      if (lc instanceof EmptyLineController) { //method end
        return swallowEmptyLines(my_doc, j, a_ctxt);
      }
      if (lc instanceof InstructionLineController) { //instruction line
        handleleInstructionLine(lc, mg, il, iter);
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
   * @throws BadLocationException in case the method reaches a line number
   *   which is not within the given document
   */
  private int swallowComment(final BytecodeDocument a_doc,
                                final int the_current_lno,
                                final int the_last_lno,
                                final LineContext a_ctxt)
    throws BadLocationException {
    int j = the_current_lno;
    while (j <= the_last_lno) {
      final String line = getLineFromDoc(a_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(line, a_ctxt);
      if (!(lc instanceof CommentLineController)) {
        break;
      }
      getEditorLines().add(j, lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      j++;
    }
    return j;
  }
}
