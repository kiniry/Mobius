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

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.swt.widgets.Shell;

import umbra.UmbraException;
import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;

/**
 * This class handles the initial parsing of a byte code textual document.
 * It creates handlers for each line of the document and structures to handle
 * the end-of-line comments. It is also able to reconstruct the end-of-line
 * comments from the previous session (closed with the refresh action).
 *
 * This class is used by {@link BytecodeController} to initialise its internal
 * structures at the beginning of editing or after the refresh action is
 * performed.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class InitParser extends BytecodeTextParser {


  /**
   * The byte code document to be parsed. It contains the corresponding BCEL
   * structures linked into it.
   */
  private BytecodeDocument my_doc;

  /**
   * This constructor initialises all the internal structures. It memorises
   * the given document and array with end-of-line comments. Furthermore,
   * it sets all the internal containers to be empty.
   *
   * @param a_doc the byte code document with the corresponding BCEL
   *   structures linked into it
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the document,
   *   if this parameter is null then the array is not taken into account
   */
  public InitParser(final BytecodeDocument a_doc,
                    final String[] a_comment_array) {
    super(a_comment_array);
    my_doc = a_doc;
  }

  /**
   * Initialisation of all the byte code structures related to
   * the document; it uses BCEL objects associated with the
   * document and based on them it generates the Umbra line
   * structures (subclasses of the {@link BytecodeLineController})
   * together with the links to the BCEL objects.
   *
   * This method initialises the parsing context, then it parses the header
   * of the class and then one by one parses the methods. At the end
   * the method initialises the structures to keep track of the modified
   * methods.
   *
   */
  public final void runParsing() {
    initInstructionNo();
    int a_line_no = 0;
    int a_method_count = 0;
    final LineContext ctxt = new LineContext();
    try {
      a_line_no = swallowClassHeader(a_line_no, ctxt);
    }  catch (BadLocationException e) {
      MessageDialog.openInformation(new Shell(), "Bytecode",
                         "The current document has no positions for line " +
                         a_line_no);
      return;
    }
    while (a_line_no < my_doc.getNumberOfLines()) {
      try {
        ctxt.incMethodNo();
        a_line_no = swallowMethod(a_line_no, a_method_count, ctxt);
      } catch (BadLocationException e) {
        MessageDialog.openInformation(new Shell(), "Bytecode",
                      "The current document has no positions for line " +
                      a_line_no);
        break;
      } catch (UmbraException e) {
        MessageDialog.openInformation(new Shell(), "Bytecode",
                      "The current document has too many methods (" +
                      a_method_count + ")");
        break;
      }
      a_method_count++;
    }
  }

  /**
   * The method parses the initial portion of a byte code text. This portion
   * contains the information about the class which the code implements.
   * The exact format is:
   * <pre>
   * public PackageName
   * [ emptylines ]
   * AccessModifier class ClassName
   * [ emptylines ]
   * </pre>
   * Note that emptylines may be comments as well.
   *
   * @param the_current_line the line from which we start the parsing (mostly 0)
   * @param a_ctxt the parsing context
   * @return the advanced line number, the first line number which has not been
   *   analysed by the current method
   * @throws BadLocationException in case one of the locations in the document
   *   was wrongly calculated
   */
  private int swallowClassHeader(final int the_current_line,
                                 final LineContext a_ctxt)
    throws BadLocationException {
    int j = the_current_line;
    String line = getLineFromDoc(my_doc, j, a_ctxt);
    a_ctxt.setInitial();
    BytecodeLineController lc = Preparsing.getType(line, a_ctxt);
    getEditorLines().add(j, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    j++;
    j = swallowEmptyLines(my_doc, j, a_ctxt);
    line = getLineFromDoc(my_doc, j, a_ctxt);
    a_ctxt.seClassToBeRead();
    lc = Preparsing.getType(line, a_ctxt);
    getEditorLines().add(j, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    j++;
    return swallowEmptyLines(my_doc, j, a_ctxt);
  }


  /**
   * This method handles the parsing of these lines of a textual representation
   * which contain a method. The method first swallows the eventual empty
   * lines before the method. Then the method checks if the method currently to
   * be parsed can fit into the structures within the BCEL representation.
   * Subsequently it parses line by line the given document starting with the
   * given line and tries to parse the lines and associate with them the
   * instructions from the BCEL structures. The current method ends when
   * an empty line is met or when the end of the document is reached.
   *
   * @param the_line_no the line in the document starting with which the method
   *   parsing begins
   * @param a_method_no the number of the method to be parsed
   * @param a_ctxt a parsing context
   * @return the number of the first line after the method; it is the first
   *   line after the empty method delimiting line or the last line in the
   *   document in case the end of document is met
   * @throws BadLocationException in case a line number is reached which is
   *   not within the given document
   * @throws UmbraException the given method number exceeds the number of
   *   available methods in the BCEL structure
   */
  private int swallowMethod(final int the_line_no,
                            final int a_method_no,
                            final LineContext a_ctxt)
    throws BadLocationException, UmbraException {
    int j = swallowEmptyLines(my_doc, the_line_no, a_ctxt);
    final MethodGen mg = getMethodGenFromDoc(my_doc, a_method_no);
    final InstructionList il = mg.getInstructionList();
    il.setPositions();
    final Iterator iter = il.iterator();

    for (; j < my_doc.getNumberOfLines(); j++) {
      final String lineName = getLineFromDoc(my_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(lineName,
                                                           a_ctxt);
      getEditorLines().add(j, lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      if (lc.isCommentStart()) { // ignore comments
        j = swallowEmptyLines(my_doc, j, a_ctxt);
        continue;
      }
      if (lc instanceof HeaderLineController) { // method header
        continue;
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

  /*@
    @ requires a_methgen.getInstructionList() == an_ilist;
    @*/
  /**
   * This method incorporates the given instruction line controller into the
   * internal structures and binds the controller with BCEL representation
   * of its instruction. The iterator {@code an_iter} iterates over the
   * instruction list {@code an_ilist} from the {@link MethodGen} object
   * in {@code a_methgen}. When the iterator has the next instruction this
   * instruction handle is associated with the given {@link BytecodeController}
   * object {@code a_lctrl} together with the given instruction list and
   * {@link MethodGen}. Except for that the method add the line controller
   * to the instructions structure and handles the comments for the line.
   *
   * @param a_lctrl the line controller which is handled
   * @param a_methgen a BCEL representation of method in which the instruction
   *   lies
   * @param an_ilist an instruction list from the method above
   * @param an_iter the iterator in the instruction list above
   */
  private void handleleInstructionLine(final BytecodeLineController a_lctrl,
                                       final MethodGen a_methgen,
                                       final InstructionList an_ilist,
                                       final Iterator an_iter) {
    InstructionHandle ih = null;
    if (an_iter.hasNext())
      ih = (InstructionHandle)(an_iter.next());
    a_lctrl.addHandle(ih, an_ilist, a_methgen);
    incInstructionNo();
    getInstructions().add(a_lctrl);
    handleComments(a_lctrl);
  }

}
