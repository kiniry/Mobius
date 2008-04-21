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

import umbra.editor.BytecodeDocument;
import umbra.editor.UmbraLocationException;
import umbra.editor.UmbraMethodException;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.ThrowsLineController;

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
public class InitParser extends BytecodeCommentParser {


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
   * @param a_interline contains the texts of interline comments, the
   *   i-th entry contains the comment for the i-th instruction in the document,
   *   if this parameter is null then the array is not taken into account
   */
  public InitParser(final BytecodeDocument a_doc,
                    final String[] a_comment_array,
                    final String[] a_interline) {
    super(a_comment_array, a_interline);
    my_doc = a_doc;
  }

  /**
   * Initialisation of all the byte code structures related to
   * the document; it uses BCEL objects associated with the
   * document and based on them it generates the Umbra line
   * structures (subclasses of the {@link BytecodeLineController})
   * together with the links to the BCEL objects. The comment
   * structures that might have come from previous sessions may cause changes
   * in the original textual representation. The method returns the changed
   * representation.
   *
   * This method initialises the parsing context, then it parses the header
   * of the class and then one by one parses the methods. At the end
   * the method initialises the structures to keep track of the modified
   * methods.
   * @return changed textual representation of the parsed class
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   * @throws UmbraMethodException thrown in case a method number has been
   *   reached which is outside the number of available methods in the document
   */
  public final String runParsing()
    throws UmbraLocationException, UmbraMethodException {
    initInstructionNo();
    int a_line_no = 0;
    int a_method_count = 0;
    final LineContext ctxt = new LineContext();
    a_line_no = swallowClassHeader(a_line_no, ctxt);
    while (a_line_no < my_doc.getNumberOfLines()) {
      ctxt.incMethodNo();
      updateAnnotations(ctxt);
      a_line_no = swallowMethod(a_line_no, a_method_count, ctxt);
      a_method_count++;
    }
    final String str = getNewContent();
    return str;
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
   * @throws UmbraLocationException in case one of the locations in the document
   *   was wrongly calculated
   */
  private int swallowClassHeader(final int the_current_line,
                                 final LineContext a_ctxt)
    throws UmbraLocationException {
    int j = the_current_line;
    String line = getLineFromDoc(my_doc, j, a_ctxt); //package
    a_ctxt.setInitial();
    BytecodeLineController lc = Preparsing.getType(line, a_ctxt);
    addEditorLine(j, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    j++;
    j = swallowEmptyLines(my_doc, j, my_doc.getNumberOfLines() - 1, a_ctxt);
                                                                  //empty lines
    line = getLineFromDoc(my_doc, j, a_ctxt); //class
    a_ctxt.setClassToBeRead();
    lc = Preparsing.getType(line, a_ctxt);
    addEditorLine(j, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    j++;
    return swallowEmptyLines(my_doc, j, my_doc.getNumberOfLines() - 1, a_ctxt);
  }

  /**
   * This method handles the parsing of these lines of a textual representation
   * which contain a method. The method first swallows the eventual empty
   * lines before the method. Then the method checks if the method currently to
   * be parsed can fit into the structures within the BCEL representation.
   * Subsequently it parses line by line the given document starting with the
   * given line and tries to parse the lines and associate with them the
   * instructions from the BCEL structures. It assumes that the method starts
   * with a method header. The current method ends when an empty line is met or
   * when the end of the document is reached.
   *
   * @param the_line_no the line in the document starting with which the method
   *   parsing begins
   * @param a_method_no the number of the method to be parsed
   * @param a_ctxt a parsing context
   * @return the number of the first line after the method; it is the first
   *   line after the empty method delimiting line or the last line in the
   *   document in case the end of document is met
   * @throws UmbraLocationException in case a line number is reached which is
   *   not within the given document
   * @throws UmbraMethodException the given method number exceeds the range of
   *   available methods in the BCEL structure
   */
  private int swallowMethod(final int the_line_no,
                            final int a_method_no,
                            final LineContext a_ctxt)
    throws UmbraLocationException, UmbraMethodException {
    int j = swallowEmptyLines(my_doc, the_line_no,
                              my_doc.getNumberOfLines() - 1, a_ctxt);
    final MethodGen mg = getMethodGenFromDoc(my_doc, a_method_no);

    //swallow method header
    j = swallowMethodHeader(a_ctxt, j, mg);

    final InstructionList il = mg.getInstructionList();
    if (il != null) {
      il.setPositions();
      final Iterator iter = il.iterator();

      for (; j < my_doc.getNumberOfLines(); j++) {
        final String  a_linename = getLineFromDoc(my_doc, j, a_ctxt);
        final BytecodeLineController lc =
          Preparsing.getType(a_linename, a_ctxt);
        addEditorLine(j, lc);
        lc.setMethodNo(a_ctxt.getMethodNo());
        if (lc.isCommentStart()) { // ignore comments
          j = swallowEmptyLines(my_doc, ++j, my_doc.getNumberOfLines() - 1,
                                a_ctxt) - 1;
          continue;
        }
        if (lc instanceof EmptyLineController) { //method end
          return swallowEmptyLines(my_doc, ++j, my_doc.getNumberOfLines() - 1,
                                   a_ctxt);
        }
        if (lc instanceof InstructionLineController) { //instruction line
          handleleInstructionLine((InstructionLineController)lc, mg, il, iter);
        }
      }
    }
    return j;
  }

  /**
   * This method handles the parsing of the method header lines. It assumes that
   * the header contains the method signature and possibly the throws
   * declarations. The method finishes its work on the first non-throws
   * line of the document.
   *
   * @param a_ctxt the parsing context with which the parsing is done
   * @param a_lineno the line number of the first line to be parsed
   * @param a_methodgen the BCEL method representation
   * @return the number of the first line that could not be parsed by this
   *   method
   * @throws UmbraLocationException in case a line number has been reached
   *   such that there is no such a line in the current document
   */
  private int swallowMethodHeader(final LineContext a_ctxt,
                                  final int a_lineno,
                                  final MethodGen a_methodgen)
    throws UmbraLocationException {
    int res = a_lineno;
    String a_linename = getLineFromDoc(my_doc, res, a_ctxt);
    BytecodeLineController lc = Preparsing.getType(a_linename, a_ctxt);
    addEditorLine(res, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    if (lc instanceof HeaderLineController) { // method header
      ((HeaderLineController)lc).setMethod(a_methodgen);
    }
    res++;
    for (a_linename = getLineFromDoc(my_doc, res, a_ctxt); true; res++) {
      lc = Preparsing.getType(a_linename, a_ctxt);
      if (lc instanceof ThrowsLineController) { // method header
        addEditorLine(res, lc);
        lc.setMethodNo(a_ctxt.getMethodNo());
      } else {
        break;
      }
    }
    return res;
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
  private void handleleInstructionLine(final InstructionLineController a_lctrl,
                                       final MethodGen a_methgen,
                                       final InstructionList an_ilist,
                                       final Iterator an_iter) {
    InstructionHandle ih = null;
    if (an_iter.hasNext())
      ih = (InstructionHandle)(an_iter.next());
    a_lctrl.addHandle(ih, an_ilist, a_methgen);
    final int ino = addInstruction(a_lctrl);
    handleComments(a_lctrl, ino);
    incInstructionNo();
  }
}
