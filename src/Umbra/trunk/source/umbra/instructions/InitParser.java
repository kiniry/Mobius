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
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Shell;

import umbra.UmbraException;
import umbra.editor.BytecodeDocument;
import umbra.editor.parsing.BytecodeStrings;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
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
public class InitParser {


  /**
   * The list of all the lines in the editor which contain codes of
   * instructions. These are represented as objects the classes of which
   * are subclasses of {@link InstructionLineController}.
   */
  private LinkedList my_instructions;

  /**
   * The list of all the lines in the current byte code editor. These lines
   * are stored as objects the classes of which are subclasses of
   * {@link BytecodeLineController}.
   */
  private LinkedList my_editor_lines;

  /**
   * This field contains the value of the end-of-line comment from the currently
   * parsed line.
   */
  private String my_current_comment;

  /**
   * The container of associations between the Umbra representation of lines
   * in the byte code editor and the end-of-line comments in these lines.
   * The comments must be absent from the line representation for their
   * correct parsing so they are held in this additional structure.
   */
  private Hashtable my_comments;

  /**
   * A temporary counter of instruction lines. It is used to synchronise the
   * currently parsed document with an old comments structure.
   */
  private int my_instruction_no;


  /**
   * The byte code document to be parsed. It contains the corresponding BCEL
   * structures linked into it.
   */
  private BytecodeDocument my_doc;


  /**
   * This field contains the texts of end-of-line comments which were introduced
   * in the previous session with, the current document. The i-th entry contains
   * the comment for the i-th instruction in the document, if this array
   * is null then the array is not taken into account.
   */
  private String[] my_comment_array;


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
    my_doc = a_doc;
    my_comment_array = a_comment_array;
    my_editor_lines = new LinkedList();
    my_instructions = new LinkedList();
    my_comments = new Hashtable();
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
    my_instruction_no = 0;
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
    my_editor_lines.add(j, lc);
    lc.setMethodNo(a_ctxt.getMethodNo());
    j++;
    j = swallowEmptyLines(my_doc, j, a_ctxt);
    line = getLineFromDoc(my_doc, j, a_ctxt);
    a_ctxt.seClassToBeRead();
    lc = Preparsing.getType(line, a_ctxt);
    my_editor_lines.add(j, lc);
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
      my_editor_lines.add(j, lc);
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
    my_instruction_no++;
    my_instructions.add(a_lctrl);
    handleComments(a_lctrl);
  }

  /**
   * This method parses from the given document lines which are considered
   * to be empty lines in the given context. A line is empty when it
   * contains white spaces only or is one of the possible kinds of
   * comment lines. The parsing stops at the first line which cannot
   * be considered empty. This line will be parsed once more by subsequent
   * parsing procedure.
   *
   * @param a_doc a document to extract empty lines from
   * @param the_current_lno the first line to be analysed
   * @param a_ctxt a parsing context in which the document is analysed
   * @return the first line which is not an empty line; in case the end
   *   of the document is reached this is the number of lines in the
   *   document
   * @throws BadLocationException in case the method reaches a line number
   *   which is not within the given document
   */
  private int swallowEmptyLines(final IDocument a_doc,
                                final int the_current_lno,
                                final LineContext a_ctxt)
    throws BadLocationException {
    int j = the_current_lno;
    while (j < a_doc.getNumberOfLines()) {
      final String line = getLineFromDoc(a_doc, j, a_ctxt);
      final BytecodeLineController lc = Preparsing.getType(line, a_ctxt);
      if (!(lc instanceof CommentLineController)  &&
          !(lc instanceof EmptyLineController)) {
        break;
      }
      my_editor_lines.add(j, lc);
      lc.setMethodNo(a_ctxt.getMethodNo());
      j++;
    }
    return j;
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
   * @throws BadLocationException in case the given line number is not within
   *   the given document
   */
  private String getLineFromDoc(final IDocument a_doc,
                                final int a_line,
                                final LineContext a_ctxt)
    throws BadLocationException {
    final String line = a_doc.get(a_doc.getLineOffset(a_line),
                                  a_doc.getLineLength(a_line));
    final String lineName;
    if (a_ctxt.isInsideComment() || a_ctxt.isInsideAnnotation()) {
      lineName = removeCommentFromLine(line);
      my_current_comment = extractCommentFromLine(line, a_ctxt);
    } else {
      lineName = line;
      my_current_comment = null;
    }
    return lineName;
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
   * The method checks if the given line contains a single line comment
   * and extracts the comment string. In case there is no
   * comment in the line, it returns <code>null</code>.
   * In case the parsing context is such that we are inside a many-line
   * comment, then the comment inside a line is always empty.
   * Additionally, this method removes the end-of-line char from the
   * string.
   *
   * @param a_line_text the line to check for my_comments
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
   * @throws UmbraException in case the given method number is wrong
   */
  private MethodGen getMethodGenFromDoc(final BytecodeDocument a_doc,
                                        final int a_method_no)
    throws UmbraException {
    final ClassGen cg = a_doc.getClassGen();
    final Method[] methods = cg.getMethods();
    if (a_method_no >= methods.length) // too many methods
      throw new UmbraException();

    final MethodGen mg = new MethodGen(methods[a_method_no], cg.getClassName(),
                                       cg.getConstantPool());
    return mg;
  }


  /**
   * This method stores in the local comments structure the information about
   * the currently extracted comment. It also handles the enriching of the
   * comments in the current version of the document with the information
   * from the previous one the content of which was refreshed.
   *
   * @param a_lc the line controller to associate the comment to
   */
  private void handleComments(final BytecodeLineController a_lc) {
    if (my_current_comment != null) {
      my_comments.put(a_lc, my_current_comment);
      my_current_comment = null;
    }
    if (my_comment_array != null) {
      if (my_comment_array[my_instruction_no] != null) {
        my_comments.put(a_lc, my_current_comment);
      }
    }
  }

  /**
   * Returns the list of all the lines in the internal representation.
   *
   * @return the list of the {@link BytecodeLineController} objects that
   *   represent all the lines in the currently parsed document
   */
  public LinkedList getEditorLines() {
    return my_editor_lines;
  }

  /**
   * Returns the list of all the lines with instructions in the internal
   * representation.
   *
   * @return the list of the {@link BytecodeLineController} objects that
   *   represent the lines with instructions in the currently parsed document
   */
  public LinkedList getInstructions() {
    return my_instructions;
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
    return my_comments;
  }
}
