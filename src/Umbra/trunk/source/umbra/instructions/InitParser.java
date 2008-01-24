/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.lang.reflect.InvocationTargetException;
import java.util.Hashtable;
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
import umbra.editor.parsing.BytecodeWhitespaceDetector;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.ThrowsLineController;
import umbra.instructions.ast.UnknownLineController;

/**
 * @author alx
 * @version a-01
 *
 */
public class InitParser {

  /**
   * The list of all the lines in the editor which contain codes of
   * instructions. These are represented as objects the classes of which
   * are subclasses of {@ref InstructionLineController}.
   */
  protected LinkedList my_instructions;


  /**
   * Keeps track of modified methods. Each time a method is modified
   * an entry with the method number is marked <code>true</code> in the array.
   */
  protected boolean[] my_modified;

  /**
   * The list of all the lines in the current byte code editor. These lines
   * are stored as objects the classes of which are subclasses of
   * {@link BytecodeLineController}.
   */
  protected LinkedList my_editor_lines;

  /**
   * This field contains the value of the inline comment from the currently
   * parsed line.
   */
  private String my_current_comment;


  /**
   * The container of all the in-line comments in the byte code document.
   */
  protected Hashtable my_comments;

  /**
   * The automaton to pre-parse the lines of the byte code document.
   */
  private DispatchingAutomaton my_preparse_automaton;

  /**
   * This is an array which contains a temporary copy of the end-of-line
   * comments used to enrich the current version of the text representation
   * obtained from the BMLLib (and BCEL) with the comments from the previous
   * one.
   */
  private String[] my_comments_temp;

  /**
   * A temporary counter of instruction lines. It is used to synchronise the
   * currently parsed document with an old comments structure.
   */
  private int my_instruction_no;


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
   * @param a_doc the byte code document with the corresponding BCEL
   *   structures linked into it
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the file,
   *   if this parameter is null then the array is not taken into account
   */
  public final void init(final BytecodeDocument a_doc,
                         final String[] a_comment_array) {
    my_comments_temp = a_comment_array;
    my_instruction_no = 0;
    int a_line_no = 0;
    int a_method_count = 0;
    final LineContext ctxt = new LineContext();
    try {
      a_line_no = swallowClassHeader(a_doc, a_line_no, ctxt);
    }  catch (BadLocationException e) {
      MessageDialog.openInformation(new Shell(), "Bytecode",
                         "The current document has no positions for line " +
                         a_line_no);
      return;
    }
    while (a_line_no < a_doc.getNumberOfLines()) {
      try {
        a_line_no = swallowMethod(a_doc, a_line_no, a_method_count, ctxt);
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

    final int methodNum = ((BytecodeLineController)my_instructions.getLast()).
                                getIndex() + 1;
    my_modified = new boolean[methodNum];
    for (a_method_count = 0; a_method_count < my_modified.length;
         a_method_count++)
      my_modified[a_method_count] = false;
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
   * @param a_doc the document to be parsed
   * @param the_current_line the line from which we start the parsing (mostly 0)
   * @param a_ctxt the parsing context
   * @return the advanced line number, the first line number which has not been
   *   analysed by the current method
   * @throws BadLocationException in case one of the locations in the document
   *   was wrongly calculated
   */
  private int swallowClassHeader(final IDocument a_doc,
                                 final int the_current_line,
                                 final LineContext a_ctxt)
    throws BadLocationException {
    int j = the_current_line;
    String line = getLineFromDoc(a_doc, j, a_ctxt);
    a_ctxt.setInitial();
    BytecodeLineController lc = getType(line, a_ctxt);
    my_editor_lines.add(j, lc);
    j++;
    j = swallowEmptyLines(a_doc, j, a_ctxt);
    line = getLineFromDoc(a_doc, j, a_ctxt);
    a_ctxt.seClassToBeRead();
    lc = getType(line, a_ctxt);
    my_editor_lines.add(j, lc);
    j++;
    return swallowEmptyLines(a_doc, j, a_ctxt);
  }


  /**
   * This method handles the parsing of these lines of a textual representation
   * which contain a method. The method first swallows the eventual empty
   * lines before the method. Then the method checks if the method currently to
   * be parsed can fit into the structures withing the BCEL representation.
   * Subsequently it parses line by line the given document starting with the
   * given line and tries to parse the lines and associate with them the
   * instructions from the BCEL structures. The current method ends when
   * an empty line is met or when the end of the document is reached.
   *
   * @param a_doc a document to parse a method from
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
  private int swallowMethod(final BytecodeDocument a_doc,
                            final int the_line_no,
                            final int a_method_no,
                            final LineContext a_ctxt)
    throws BadLocationException, UmbraException {
    int j = swallowEmptyLines(a_doc, the_line_no, a_ctxt);
    final MethodGen mg = getMethodGenFromDoc(a_doc, a_method_no);
    final InstructionList il = mg.getInstructionList();
    final InstructionHandle ih = il.getStart();
    int ic = my_instructions.size(); // counts lines with instructions

    for (; j < a_doc.getNumberOfLines(); j++) {
      final String lineName = getLineFromDoc(a_doc, j, a_ctxt);
      final BytecodeLineController lc = getType(lineName, a_ctxt);
      if (lc.isCommentStart()) { // ignore comments
        j = swallowEmptyLines(a_doc, j, a_ctxt);
        continue;
      }
      my_editor_lines.add(j, lc);
      if (lc instanceof HeaderLineController) { // method header
        continue;
      }
      if (lc instanceof EmptyLineController) { //method end
        return swallowEmptyLines(a_doc, j, a_ctxt);
      }
      if (lc.addHandle(ih, il, mg, a_method_no - 1)) { //instruction line
        my_instruction_no++;
        my_instructions.add(ic++, lc);
        handleComments(lc);
      }
    }
    return j;
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
      final BytecodeLineController lc = getType(line, a_ctxt);
      if (!(lc instanceof CommentLineController)  &&
          !(lc instanceof EmptyLineController)) {
        break;
      }
      my_editor_lines.add(j, lc);
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
   * Removes an one-line comment from a line of bytecode.
   *
   * @param a_line a line of bytecode
   * @return the bytecode line without one-line comment and final whitespaces
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
    final String nl = a_line_text.substring(i +
                                  BytecodeStrings.SINGLE_LINE_COMMENT_MARK_LEN,
                                  a_line_text.indexOf("\n"));
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
    if (my_comments_temp != null) {
      if (my_comments_temp[my_instruction_no] != null) {
        my_comments.put(a_lc, my_current_comment);
      }
    }
  }

  /**
   * TODO
   * @return
   */
  private DispatchingAutomaton getAutomaton() {
    if (my_preparse_automaton == null) {
      my_preparse_automaton = new DispatchingAutomaton();
      my_preparse_automaton.addSimple("", EmptyLineController.class);
      addWhitespaceLoop(my_preparse_automaton);
      addSimpleForArray(BytecodeStrings.THROWS_PREFIX,
                        ThrowsLineController.class);
      addSimpleForArray(BytecodeStrings.HEADER_PREFIX,
                        HeaderLineController.class);
      my_preparse_automaton.addSimple(BytecodeStrings.COMMENT_LINE_START,
                                      CommentLineController.class);
      my_preparse_automaton.addSimple(BytecodeStrings.ANNOT_LINE_START,
                                      AnnotationLineController.class);
      final DispatchingAutomaton digitnode = my_preparse_automaton.
               addSimple("0",
                         UnknownLineController.class);
      for (int i = 1; i < 10; i++) {
        my_preparse_automaton.addStarRule(Integer.toString(i), digitnode);
      }
      for (int i = 0; i < 10; i++) {
        my_preparse_automaton.addStarRule("0" + Integer.toString(i), digitnode);
      }
      final DispatchingAutomaton colonnode = digitnode.addSimple(":",
                                               UnknownLineController.class);
      addWhitespaceLoop(colonnode);
      addAllMnemonics(colonnode);
    }
    return my_preparse_automaton;
  }

  private void addSimpleForArray(final String[] sHeaderInits,
                                 final Class a_class) {
    for (int k = 0; k < sHeaderInits.length; k++) {
      my_preparse_automaton.addSimple(sHeaderInits[k],
                                      a_class);
    }
  }

  private static void addWhitespaceLoop(DispatchingAutomaton an_automaton) {
    for (int i = 0;
         i < BytecodeWhitespaceDetector.WHITESPACE_CHARACTERS.length;
         i++) {
      an_automaton.addStarRule(
        Character.toString(BytecodeWhitespaceDetector.
                           WHITESPACE_CHARACTERS[i]),
        an_automaton);
    }
  }

  private void addAllMnemonics(final DispatchingAutomaton colonnode) {
    for (int i = 0; i < InstructionLineController.INS_CLASS_HIERARCHY.length;
         i++) {
      try {
        final String[] the_mnemonics = (String[])
            (InstructionLineController.INS_CLASS_HIERARCHY[i].
                getMethod("getMnemonics").invoke(null));
        for (int j = 0; j < the_mnemonics.length; j++) {
          colonnode.addMnemonic(the_mnemonics[j], the_mnemonics[j],
                             InstructionLineController.INS_CLASS_HIERARCHY[i]);
        }
      } catch (IllegalArgumentException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (SecurityException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (IllegalAccessException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (InvocationTargetException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (NoSuchMethodException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
  }

  /**
   * Chooses one of line types that matches the given line
   * contents. This method does a quick pre-parsing of the
   * line content and based on that chooses which particular line controller
   * should be used for the given line. It also uses the context information
   * to return controllers in case the analysis is inside a comment or a
   * BML annotation.
   *
   * @param a_line the string contents of inserted or modified line
   * @param a_context information on the previous lines
   * @return instance of subclass of a line controller
   *     that contents of the given line satisfies
   *     classification conditions (unknown if it does not for all)
   */
  protected BytecodeLineController getType(final String a_line,
                                         final LineContext a_context) {
    if (a_context.isInsideComment()) {
      final CommentLineController lc = new CommentLineController(a_line);
      if (lc.isCommentEnd()) {
        a_context.revertState();
      }
      return lc;
    }

    if (a_context.isInsideAnnotation()) {
      final AnnotationLineController lc = new AnnotationLineController(a_line);
      if (lc.isCommentEnd()) {
        a_context.revertState();
      }
      return lc;
    }
    final DispatchingAutomaton automaton = getAutomaton();
    BytecodeLineController  blc;
    try {
      blc = automaton.execForString(a_line, a_line);
    } catch (CannotCallRuleException e) {
      blc = new UnknownLineController(a_line);
    }
    if (blc instanceof CommentLineController) {
      if (blc instanceof AnnotationLineController) {
        a_context.setInsideAnnotation();
      } else {
        a_context.setInsideComment();
      }
    }
    return blc;
  }

  /**
   * This method strips off the whitespace characters both at the beginning
   * and at the end of the given string. It works similarly to
   * {@ref String#trim()}, but it uses the local definition of the whitespace
   * as in {@ref BytecodeWhitespaceDetector}.
   *
   * @param a_string to strip off the whitespace
   * @return the string with no whitespace
   */
  private static String removeWhiteSpace(/*@ non_null @*/ final String a_string) {
    String res = "";
    if (a_string.length() != 0) {
      final BytecodeWhitespaceDetector wd = new BytecodeWhitespaceDetector();
      int i = 0;
      boolean ok = true;
      //count whitespace at the beginning
      while (ok && i < a_string.length()) {
        if (!wd.isWhitespace(a_string.charAt(i))) ok = false;
        i++;
      }
      if (!ok) { //not only whitespace in the string
        int j = a_string.length();
        ok = true;
        //count whitespace at the end
        while (ok && j > 0) {
          j--;
          if (!wd.isWhitespace(a_string.charAt(j))) ok = false;
        }
        if (!ok) res = a_string.substring(i - 1, j + 1);
      }
    }
    return res;
  }

}
