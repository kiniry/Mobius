/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.Hashtable;
import java.util.LinkedList;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Shell;

import umbra.UmbraException;
import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import umbra.editor.BytecodeDocument;
import umbra.editor.parsing.BytecodeStrings;
import umbra.editor.parsing.BytecodeStringsGeneric;
import umbra.editor.parsing.BytecodeWhitespaceDetector;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.ArithmeticInstruction;
import umbra.instructions.ast.ArrayInstruction;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.ConversionInstruction;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.FieldInstruction;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.IConstInstruction;
import umbra.instructions.ast.IncInstruction;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.InvokeInstruction;
import umbra.instructions.ast.JumpInstruction;
import umbra.instructions.ast.LdcInstruction;
import umbra.instructions.ast.LoadStoreArrayInstruction;
import umbra.instructions.ast.LoadStoreConstInstruction;
import umbra.instructions.ast.NewInstruction;
import umbra.instructions.ast.PushInstruction;
import umbra.instructions.ast.SingleInstruction;
import umbra.instructions.ast.StackInstruction;
import umbra.instructions.ast.ThrowsLineController;
import umbra.instructions.ast.UnclassifiedInstruction;
import umbra.instructions.ast.UnknownLineController;

/**
 * This class defines some structures related to BCEL as well
 * as to the byte code editor contents. The structures are updated after
 * each byte code modification and its modification allow
 * updating BCEL. Especially a list of all lines (on purpose to
 * check correctness) as well as a list of instruction lines
 * to detect when BCEL modification is needed. Additional
 * structures keep the information which method has been
 * modified (in case of combining changes) and what comments
 * are added to byte code
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeController {

  /**
   * The list of all the lines in the current byte code editor. These lines
   * are stored as objects the classes of which are subclasses of
   * {@link BytecodeLineController}.
   */
  private LinkedList my_editor_lines;

  /**
   * The list of all the lines in the editor which contain codes of
   * instructions. These are represented as objects the classes of which
   * are subclasses of {@ref InstructionLineController}.
   */
  private LinkedList my_instructions;

  /**
   * The list of all the lines which were detected to be incorrect.
   */
  private LinkedList my_incorrect;

  /**
   * The container of all the in-line comments in the byte code document.
   */
  private Hashtable my_comments;

  /**
   * The container of all the multi-line comments. Each element of the table is
   * an association between a list
   */
  private Hashtable my_interline;

  /**
   * Keeps track of modified methods. Each time a method is modified
   * an entry with the method number is marked <code>true</code> in the array.
   */
  private boolean[] my_modified;

  /**
   * This field contains the value of the inline comment from the currently
   * parsed line.
   */
  private String my_current_comment;

  /**
   * The automaton to pre-parse the lines of the byte code document.
   */
  private DispatchingAutomaton my_preparse_automaton;

  private String[] my_comments_temp;

  private int my_instruction_no;

  /**
   * The constructor which initialises all the internal containers to be
   * empty.
   */
  public BytecodeController() {
    super();
    my_editor_lines = new LinkedList();
    my_instructions = new LinkedList();
    my_incorrect = new LinkedList();
    my_comments = new Hashtable();
    my_interline = new Hashtable();
  }

  /**
   * This is a debugging method. It prints out to the standard output the
   * list of all the instructions in the controller.
   */
  public final void showInstructionList() {
    for (int i = 0; i < my_editor_lines.size(); i++) {
      UmbraPlugin.LOG.print(
                ((BytecodeLineController)(my_editor_lines.get(i))).
                                  getMy_line_text());
    }
  }

  /**
   * This method prints out to the standard output the
   * list of all the incorrect instructions in the controller.
   */
  public final void showAllIncorrectLines()
  {
    UmbraPlugin.messagelog("" + my_incorrect.size() + " incorrects:");
    UmbraPlugin.LOG.flush();
    for (int i = 0; i < my_incorrect.size(); i++) {
      UmbraPlugin.messagelog(" " +
             ((BytecodeLineController)(my_incorrect.get(i))).getMy_line_text());
    }
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
   * @param a_doc the byte code document with the corresponding BCEL
   *   structures linked into it
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the file,
   *   if this parameter is null then the array is not taken into account
   */
  public final void init(final IDocument a_doc,
                         final String[] a_comment_array) {
    // i - iterates over methods
    // j - iterates over lines in the document
    my_comments_temp = a_comment_array;
    my_instruction_no = 0;
    int j = 0;
    int i = 0;
    final LineContext ctxt = new LineContext();
    try {
      j = swallowClassHeader(a_doc, j, ctxt);
    }  catch (BadLocationException e) {
      MessageDialog.openInformation(new Shell(), "Bytecode",
                         "The current document has no positions for line " + j);
    }
    while (j < a_doc.getNumberOfLines() - 1) {
      try {
        j = swallowMethod(a_doc, j, i, ctxt);
      } catch (BadLocationException e) {
        MessageDialog.openInformation(new Shell(), "Bytecode",
                      "The current document has no positions for line " + j);
      } catch (UmbraException e) {
        MessageDialog.openInformation(new Shell(), "Bytecode",
                      "The current document has too many methods (" + i + ")");
      }
      i++;
    }

    final int methodNum = ((BytecodeLineController)my_instructions.getLast()).
                                getIndex() + 1;
    my_modified = new boolean[methodNum];
    for (i = 0; i < my_modified.length; i++)
      my_modified[i] = false;
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
      my_editor_lines.add(j, lc);
      if (!(lc instanceof CommentLineController)  &&
          !(lc instanceof EmptyLineController)) {
        break;
      }
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
   * This method handles the parsing of these lines of a textual representation
   * which contain a method. The method checks if the method currently to be
   * parsed can fit into the structures withing the BCEL representation.
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
  private int swallowMethod(final IDocument a_doc,
                            final int the_line_no,
                            final int a_method_no,
                            final LineContext a_ctxt)
    throws BadLocationException, UmbraException {
    int j = the_line_no;
    final ClassGen cg = ((BytecodeDocument)a_doc).getClassGen();
    final Method[] methods = cg.getMethods();
    int ic = my_instructions.size(); // counts lines with instructions
    if (a_method_no >= methods.length) // too many methods
      throw new UmbraException();

    final MethodGen mg = new MethodGen(methods[a_method_no], cg.getClassName(),
                                       cg.getConstantPool());
    final InstructionList il = mg.getInstructionList();
    final InstructionHandle ih = il.getStart();

    for (; j < a_doc.getNumberOfLines() - 1; j++) {
      final String lineName = getLineFromDoc(a_doc, j, a_ctxt);
      final BytecodeLineController lc = getType(lineName, a_ctxt);
      if (lc.isCommentStart()) { // ignore comments
        j = swallowEmptyLines(a_doc, j, a_ctxt) - 1;
        continue;
      }
      my_editor_lines.add(j, lc);
      if (lc instanceof HeaderLineController) { // method header
        continue;
      }
      if (lc instanceof EmptyLineController) { //method end
        return ++j;
      }
      if (lc.addHandle(ih, il, mg, a_method_no - 1)) { //instruction line
        my_instruction_no++; TODO - partially implemented refresh of eol comments
        my_instructions.add(ic++, lc);
        handleComments(lc);
      }
    }
    return j;
  }

  /**
   * This method stores in the local comments structure the information about
   * the currently extracted comment.
   *
   * @param a_lc the line controller to associate the comment to
   */
  private void handleComments(final BytecodeLineController a_lc) {
    if (my_current_comment != null) {
      my_comments.put(a_lc, my_current_comment);
      my_current_comment = null;
    }
  }

  /**
   * The method removes from the collection of the incorrect lines
   * all the lines which are between <code>a_start</code> and
   * <code>a_stop</code>.
   *
   * @param a_start the first line which is checked for removing
   * @param a_stop the last line which is checked for removing
   */
  public final void removeIncorrects(final int a_start, final int a_stop) {
    for (int i = a_start; i <= a_stop; i++) {
      final BytecodeLineController line =
                                 (BytecodeLineController)my_editor_lines.get(i);
      if (my_incorrect.contains(line)) {
        my_incorrect.remove(line);
      }
    }
  }

  /**
   * The method detects which kind of modification (adding lines,
   * removing lines or both) has been made and performs appropriate action
   * to the byte code structures of the given byte code document.
   *
   * @param a_doc a byte code document in which the modification have
   *      been made to
   * @param a_start_rem a number of the first modified line as counted in the
   *                    old version of the document
   * @param an_end_rem a number of the last modified line as counted in the
   *                   old version of the document
   * @param a_stop a number of the last modified line as counted in the new
   *               version of the document
   */
  public final void addAllLines(final IDocument a_doc,
              final int a_start_rem, final int an_end_rem, final int a_stop)
  {
    final ClassGen cg = ((BytecodeDocument)a_doc).getClassGen();
    // i - index in the removed lines
    // j - index in the inserted lines
    for (int i = a_start_rem, j = a_start_rem;
         (i <= an_end_rem || j <= a_stop) && i < my_editor_lines.size();
         i++, j++) {
      final BytecodeLineController oldlc =
                                 (BytecodeLineController)my_editor_lines.get(j);
      BytecodeLineController a_next_line = null;
      final int off = getInstructionOff(j);
      boolean the_last_flag = false;
      final boolean metEnd = (isEnd(j)) &&
               (oldlc.getIndex() ==
                ((InstructionLineController)my_instructions.
                             get(off)).getIndex());
      if (metEnd) {
        if (isFirst(j)) {
          the_last_flag = true;
          a_next_line = (BytecodeLineController)my_instructions.get(off);
        } else
          a_next_line = (BytecodeLineController)my_instructions.get(off - 1);
      } else //TODO poprawnie: 1 enter przed wpisaniem 2 wpisac przed ta przed
             //ktora checmy wstawic i enter; zle inaczej: enter przed i potem
             //wpisac
        a_next_line = (BytecodeLineController)my_instructions.get(off + 1);
      my_modified[a_next_line.getIndex()] = true;
      if (a_start_rem <= j && j <= a_stop) { //we are in the area of inserted
                                             //lines
        try {
          i = addInstructions(a_doc, a_start_rem, an_end_rem, i, j, oldlc,
                    a_next_line, the_last_flag, metEnd, new LineContext());
        } catch (UmbraException e) {
          MessageDialog.openInformation(new Shell(), "Bytecode",
                      "A jump instruction has improper destination");
          break;
        }
      } else { // we are beyond the area of the inserted instructions
        if (a_start_rem <= i && i <= an_end_rem) {
          oldlc.dispose(a_next_line, cg, the_last_flag, my_instructions, off);
          my_editor_lines.remove(oldlc);
          j--;
        }
      }
    }
    if (UmbraHelper.DEBUG_MODE) controlPrint(1);
    return;
  }

  /**
   * TODO.
   *
   * @param a_doc bytecode document for which the changes are analysed
   * @param a_start_of_rem the beginning of the removed area
   * @param an_end_rem the end of the removed area
   * @param a_i TODO
   * @param a_j TODO
   * @param an_old_lc TODO
   * @param the_next_line TODO
   * @param the_last_flag TODO
   * @param the_methend_flag true when <code>a_j</code> is the last instruction
   *        in a method
   * @param a_context the context of the currently added instruction line
   * @return TODO
   * @throws UmbraException TODO
   */
  private int addInstructions(final IDocument a_doc,
                              final int a_start_of_rem,
                              final int an_end_rem,
                              final int a_i,
                              final int a_j,
                              final BytecodeLineController an_old_lc,
                              final BytecodeLineController the_next_line,
                              final boolean the_last_flag,
                              final boolean the_methend_flag,
                              final LineContext a_context)
    throws UmbraException {
    int res = a_i;
    final ClassGen cg = ((BytecodeDocument)a_doc).getClassGen();
    final int off = getInstructionOff(a_j);
    try {
      final String line = a_doc.get(a_doc.getLineOffset(a_j),
                                    a_doc.getLineLength(a_j));
      //%%
      final String lineName = removeCommentFromLine(line);
      final String comment = extractCommentFromLine(line, a_context);
      final BytecodeLineController lc = getType(lineName, a_context);
      lc.setIndex(((BytecodeLineController)my_editor_lines.get(a_j - 1)).
                                                           getIndex());
      if (comment != null) my_comments.put(lc, comment);
      final Instruction ins = lc.getInstruction();
      if (ins != null) {
        lc.setTarget(the_next_line.getList(), ins);
      } else {
        if (comment != null) my_interline.put(the_next_line, comment);
      }
      if (res >= a_start_of_rem && res <= an_end_rem) {
        lc.update(an_old_lc, the_next_line, cg, ins, the_methend_flag,
                  the_last_flag, my_instructions, off);
        my_editor_lines.set(a_j, lc);
      } else {
        if (an_old_lc.getHandle() == null)
          lc.initHandle(the_next_line, cg, ins, the_methend_flag,
                        my_instructions, off);
        else
          lc.initHandle(an_old_lc, cg, ins, the_methend_flag,
                        my_instructions, off);
        my_editor_lines.add(a_j, lc);
        res--;
      }
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
    return res;
  }

  /**
   * Checks whether all lines of a selected area are correct
   * (they satisfies some given syntax conditions). TODO check
   *
   * @param a_start the beginning of the area
   * @param an_end the end of the area
   * @return <code>true</code> if all lines of the area are correct,
   *   <code>false</code> otherwise
   */
  public final boolean checkAllLines(final int a_start,
                                     final int an_end)
  {
    boolean ok = true;
    for (int i = a_start; i <= an_end; i++) {
      final BytecodeLineController line =
                               (BytecodeLineController)(my_editor_lines.get(i));
      if (!line.correct()) {
        System.out.println("incorrect line=" + line.getLineContent());
        ok = false;
        my_incorrect.addLast(my_editor_lines.get(i));
      }
    }
    return ok;
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
  private BytecodeLineController getType(final String a_line,
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
   * TODO
   * @return
   */
  private DispatchingAutomaton getAutomaton() {
    if (my_preparse_automaton == null) {
      my_preparse_automaton = new DispatchingAutomaton();
      my_preparse_automaton.addSimple("", EmptyLineController.class);
      for (int i = 0;
           i < BytecodeWhitespaceDetector.WHITESPACE_CHARACTERS.length;
           i++) {
        my_preparse_automaton.addStarRule(
          Character.toString(BytecodeWhitespaceDetector.
                             WHITESPACE_CHARACTERS[i]),
          my_preparse_automaton);
      }
      my_preparse_automaton.addSimple("throws", ThrowsLineController.class);
      my_preparse_automaton.addSimple("Exception", ThrowsLineController.class);
      my_preparse_automaton.addSimple("From", ThrowsLineController.class);

      final String[] sHeaderInits =  BytecodeStrings.HEADER_PREFIX;
      for (int k = 0; k < sHeaderInits.length; k++) {
        my_preparse_automaton.addSimple(sHeaderInits[k],
                                        HeaderLineController.class);
      }
      my_preparse_automaton.addSimple(BytecodeStrings.COMMENT_LINE_START,
                                      CommentLineController.class);
      my_preparse_automaton.addSimple(BytecodeStrings.ANNOT_LINE_START,
                                      AnnotationLineController.class);
      final DispatchingAutomaton digitnode = my_preparse_automaton.
               addSimple("1",
                         UnknownLineController.class);
      for (int i = 2; i < 10; i++) {
        my_preparse_automaton.addStarRule(Integer.toString(i), digitnode);
      }
      for (int i = 0; i < 10; i++) {
        my_preparse_automaton.addStarRule("1" + Integer.toString(i), digitnode);
      }
      final DispatchingAutomaton colonnode = digitnode.addSimple(":",
                                               UnknownLineController.class);
      for (int i = 0;
           i < BytecodeWhitespaceDetector.WHITESPACE_CHARACTERS.length;
           i++) {
        colonnode.addStarRule(Character.toString(BytecodeWhitespaceDetector.
                                                 WHITESPACE_CHARACTERS[i]),
                              colonnode);
      }
      addMnemonics(colonnode, BytecodeStrings.ARITHMETIC_INS,
                   ArithmeticInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.ICONST_INS,
                   IConstInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.LOAD_STORE_INS,
                   LoadStoreConstInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.LOAD_STORE_ARRAY_INS,
                   LoadStoreArrayInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.CONV_INS,
                   ConversionInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.SINGLE_INS,
                   SingleInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.PUSH_INS,
                   PushInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.JUMP_INS,
                   JumpInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.INCC_INS,
                   IncInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.STACK_INS,
                   StackInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.ARRAY_INS,
                   ArrayInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.NEW_INS,
                   NewInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.FIELD_INS,
                   FieldInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.INVOKE_INS,
                   InvokeInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.LDC_INS,
                   LdcInstruction.class);
      addMnemonics(colonnode, BytecodeStrings.UNCLASSIFIED_INS,
                   UnclassifiedInstruction.class);
    }
    return my_preparse_automaton;
  }

  /**
   * 
   * @param a_node
   * @param the_mnemonics
   * @param a_class
   */
  private void addMnemonics(final DispatchingAutomaton a_node,
                            final String[] the_mnemonics,
                            final Class a_class) {
    for (int j = 0; j < the_mnemonics.length; j++) {
      a_node.addMnemonic(the_mnemonics[j], the_mnemonics[j],
                              a_class);
    }
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
  private String removeWhiteSpace(/*@ non_null @*/ final String a_string) {
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

  /**
   * Removes an one-line comment from a line of bytecode.
   *
   * @param a_line a line of bytecode
   * @return the bytecode line without one-line comment and final whitespaces
   */
  protected final String removeCommentFromLine(final String a_line) {
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
   * This method strips off the starting numbers, then the colon
   * character (":") and then the whitespace characters.
   *
   * @param a_string the string to strip the initial characters from
   * @return TODO
   */
  protected final String removeColonFromLine(final String a_string) {
    int i = 0;
    while ((i < a_string.length()) && (Character.isDigit(a_string.charAt(i))))
      i++;
    if ((i < a_string.length()) && (a_string.charAt(i) == ':'))
      i++;
    while ((i < a_string.length()) &&
           (Character.isWhitespace(a_string.charAt(i))))
      i++;
    return a_string.substring(i, a_string.length());
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
  private String extractCommentFromLine(final String a_line_text,
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
   * @return <code>true</code> if there is no incorrect line within the whole
   *         document
   */
  public final boolean allCorrect() {
    return my_incorrect.isEmpty();
  }

  /**
   * @return number of a line that the first error occurs
   * (not necessarily: number of the first line that an error occurs)
   */
  public final int getFirstError() {
    return my_editor_lines.lastIndexOf(my_incorrect.getFirst());
  }

  /**
   * The method finds index in the instruction array that is linked with
   * the position in the line array. TODO check
   *
   * @param a_linenum line number (including all lines in a document)
   * @return instruction offset (including only instruction lines)
   *   or -1 if the line is not an instruction
   */
  private int getInstructionOff(final int a_linenum) {
    for (int i = a_linenum; i >= 0; i--) {
      final Object line = my_editor_lines.get(i);
      if (my_instructions.contains(line))
        return my_instructions.indexOf(line);
    }
    return -1;
  }

  /**
   * @param a_linenum a number of a line (including all lines in the textual
   *    representation)
   * @return <code>true</code> if <code>a_linenum</code> is a number of an
   *     instruction in {@ref #my_instructions} array that is the last
   *     instruction in a method or is a non-istruction one located after the
   *     method
   */
  private boolean isEnd(final int a_linenum) {
    final int off = getInstructionOff(a_linenum);
    if (off + 1 >= my_instructions.size()) return true;
    if (off == -1) return false;
    final int index1 = ((BytecodeLineController)my_instructions.get(off)).
                                                             getIndex();
    final int index2 = ((BytecodeLineController)my_instructions.get(off + 1)).
             getIndex();
    return (index1 != index2);
  }

  /**
   * @param a_linenum a numebr of a line (including all lines)
   * @return <code>true</code> if the line is located before the first
   *         instruction in a method TODO any method or a fixed method?
   */
  private boolean isFirst(final int a_linenum) {
    final int off = getInstructionOff(a_linenum);
    if (off == 0) return true;
    final int index1 = ((BytecodeLineController)my_instructions.get(off)).
                                                             getIndex();
    final int index2 = ((BytecodeLineController)my_instructions.get(off - 1)).
                                                             getIndex();
    return (index1 != index2);
  }

  /**
   * TODO.
   * @return TODO
   */
  public final boolean[] getModified() {
    return my_modified;
  }

  /**
   * @param the_modified the array that indicates which methods were modified
   */
  public final void setModified(final boolean[] the_modified) {
    this.my_modified = the_modified;
  }

  /**
   * Transforms a map from lines to my_comments into string array.
   * TODO
   * @return Array of my_comments
   */
  public final String[] getComments() {
    final String[] commentTab = new String[my_instructions.size()];
    for (int i = 0; i < my_instructions.size(); i++) {
      final Object lc = my_instructions.get(i);
      final String com = (String)my_comments.get(lc);
      commentTab[i] = com;
    }
    return commentTab;
  }

  /**
   * TODO.
   * @return TODO
   */
  public final String[] getInterline() {
    final String[] commentTab = new String[my_instructions.size()];
    for (int i = 0; i < my_instructions.size(); i++) {
      final Object lc = my_instructions.get(i);
      final String com = (String)my_interline.get(lc);
      commentTab[i] = com;
    }
    return commentTab;
  }

  /**
   * This is a helper method used for debugging purposes. It prints out
   * all the instructions in the internal Umbra representation of a class
   * file.
   *
   * @param an_index the number which allows to make different printouts
   */
  private void controlPrint(final int an_index) {
    UmbraPlugin.messagelog("");
    UmbraPlugin.messagelog("Control print of bytecode modification (" +
                           an_index + "):");
    for (int i = 0; i < my_instructions.size(); i++) {
      final InstructionLineController line =
                              (InstructionLineController)my_instructions.get(i);
      if (line == null) {
        UmbraPlugin.messagelog("" + i + ". null");
        return;
      }
      //if (line.index == index) {
      UmbraPlugin.messagelog("" + i + ". " + line.getName());
      final InstructionHandle ih = line.getHandle();
      if (ih == null) UmbraPlugin.messagelog("  handle - null");
      else {
        UmbraPlugin.LOG.print("  handle(" + ih.getPosition() + ") ");
        final Instruction ins = ih.getInstruction();
        if (ins == null) UmbraPlugin.LOG.print("null instruction");
        else UmbraPlugin.LOG.print(ins.getName());
        if (ih.getNext() == null) UmbraPlugin.LOG.print(" next: null");
        else UmbraPlugin.LOG.print(" next: " + ih.getNext().getPosition());
        if (ih.getPrev() == null) UmbraPlugin.messagelog(" prev: null");
        else UmbraPlugin.messagelog(" prev: " + ih.getPrev().getPosition());
      }
      //}
    }
  }
}
