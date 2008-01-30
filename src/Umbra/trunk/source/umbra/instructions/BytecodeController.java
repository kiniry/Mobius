/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MethodGen;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Shell;

import umbra.UmbraException;
import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;

/**
 * This class defines some structures related to BCEL as well
 * as to the byte code editor contents. The structures are updated after
 * each byte code modification and its modification allow
 * updating BCEL. Especially a list of all lines (on purpose to
 * check correctness) as well as a list of instruction lines
 * to detect when BCEL modification is needed. Additional
 * structures keep the information which method has been
 * modified (in case of combining changes) and what comments
 * are added to byte code.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class BytecodeController {

  /**
   * The list of all the lines in the current byte code editor. These lines
   * are stored as objects the classes of which are subclasses of
   * {@link BytecodeLineController}.
   */
  private LinkedList my_editor_lines;

  /**
   * The list of all the lines in the editor which contain codes of
   * instructions. These are represented as objects the classes of which
   * are subclasses of {@link InstructionLineController}.
   */
  private LinkedList my_instructions;

  /**
   * The list of all the lines which were detected to be incorrect.
   */
  private LinkedList my_incorrect;

  /**
   * Keeps track of modified methods. Each time a method is modified
   * an entry with the method number is marked <code>true</code> in the array.
   */
  private boolean[] my_modified;

  /**
   * The container of all the multi-line comments. Each element of the table is
   * an association between a list
   */
  private Hashtable my_interline;

  /**
   * The container of associations between the Umbra representation of lines
   * in the byte code editor and the end-of-line comments in these lines.
   * The comments must be absent from the line representation for their
   * correct parsing so they are held in this additional structure.
   */
  private Hashtable my_comments;

  /**
   * The constructor which initialises all the internal containers to be
   * empty.
   */
  public BytecodeController() {
    super();
    my_incorrect = new LinkedList();
    my_interline = new Hashtable();
  }

  /**
   * This is a debugging method. It prints out to the standard output the
   * list of all the instructions in the controller.
   */
  public void showInstructionList() {
    for (int i = 0; i < my_editor_lines.size(); i++) {
      UmbraPlugin.LOG.print(
                ((BytecodeLineController)(my_editor_lines.get(i))).
                                  getMy_line_text());
    }
  }

  /*@
    @ requires UmbraHelper.DEBUG_MODE;
    @*/
  /**
   * This method prints out to the standard output the
   * list of all the incorrect instructions in the controller. We assume the
   * calls to this method are guarded by checks of
   * {@link UmbraHelper#DEBUG_MODE}.
   */
  public void showAllIncorrectLines()
  {
    UmbraPlugin.messagelog("showAllIncorrectLines" + my_incorrect.size() +
                             " incorrects:");
    for (int i = 0; i < my_incorrect.size(); i++) {
      UmbraPlugin.messagelog(" " +
             ((BytecodeLineController)(my_incorrect.get(i))).getMy_line_text());
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
  public void removeIncorrects(final int a_start, final int a_stop) {
    for (int i = a_start; i <= a_stop; i++) {
      final BytecodeLineController line =
                                 (BytecodeLineController)my_editor_lines.get(i);
      if (my_incorrect.contains(line)) {
        my_incorrect.remove(line);
      }
    }
  }

  /**
   * The method rearranges the internal representation of the byte code
   * document to take into account the given change in the document.
   *
   * This method parses the range of TODO
   *
   * @param a_doc a byte code document in which the modification has
   *   been made
   * @param a_start_rem a number of the first modified line as counted in the
   *   old version of the document
   * @param an_end_rem a number of the last modified line as counted in the
   *   old version of the document
   * @param a_stop a number of the last modified line as counted in the new
   *   version of the document
   */
  public void addAllLines(final IDocument a_doc,
              final int a_start_rem, final int an_end_rem, final int a_stop)
  {
    final int methodno = ((BytecodeLineController)my_editor_lines.
        get(a_start_rem)).getMethodNo();
    final FragmentParser fgmparser = new FragmentParser(
      (BytecodeDocument)a_doc, a_start_rem, a_stop, methodno, null);
    fgmparser.runParsing(); // after that I must know all the instructions are
                            //correct
    updateInstructions(a_start_rem, an_end_rem, fgmparser.getInstructions());
    updateComments(a_start_rem, an_end_rem, a_stop, fgmparser.getComments());
    try {
      updateEditorLines(a_start_rem, an_end_rem, a_stop,
                        fgmparser.getEditorLines());
    } catch (UmbraException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    if (UmbraHelper.DEBUG_MODE) controlPrint(1);
    return;
  }

  private void updateComments(int a_start_rem, 
                              int an_end_rem, 
                              int a_stop,
                              Hashtable comments) {
    for (int i = a_start_rem; i <= an_end_rem; i++) {
      final Object o = my_editor_lines.get(i);
      my_comments.remove(o);
    }
    for (final Enumeration enumer = comments.keys();
         enumer.hasMoreElements();) {
      final Object key = enumer.nextElement();
      final Object value = comments.get(key);
      my_comments.put(key, value);
    }
  }

  private void updateInstructions(int a_start_rem, int an_end_rem,
                                  LinkedList instructions) {
    int first = -1;
    for (int i = a_start_rem; i <= an_end_rem; i++) {
      Object o = my_editor_lines.get(i);
      if (first < 0) {
        first = my_instructions.indexOf(o);
      }
      my_instructions.remove(o);
    }
    my_instructions.addAll(first, instructions);
  }

  private void updateEditorLines(final int a_start_rem,
                                 final int an_end_rem,
                                 final int a_stop,
                                 final LinkedList editorLines)
    throws UmbraException {
    final MethodGen mg = getCurrentMethodGen(a_start_rem, an_end_rem);
    int j = 0; // iterates over editorLines
    for (int i = a_start_rem; i <= an_end_rem && i <= a_stop; i++, j++) {
      //we replace for the common part
      final InstructionLineController oldlc =
        (InstructionLineController)my_editor_lines.get(i);
      final InstructionLineController newlc =
        (InstructionLineController)editorLines.get(j);
      oldlc.replace(newlc);
      my_editor_lines.remove(i);
      my_editor_lines.add(newlc);
    }
    if (an_end_rem < a_stop) { //we must add the new lines
      int pos = getCurrentPositionInMethod(an_end_rem + 1);
      for (int i = an_end_rem + 1; i <= a_stop; i++, j++, pos++) {
        final InstructionLineController newlc =
          (InstructionLineController)editorLines.get(j);
        newlc.addHandle(mg, pos);
      }
    } else if (an_end_rem > a_stop) { //we must remove the deleted lines
      for (int i = a_stop + 1; i <= an_end_rem; i++) {
        final InstructionLineController oldlc =
          (InstructionLineController)my_editor_lines.get(i);
        oldlc.dispose();
      }
    }
    my_editor_lines.addAll(a_start_rem, editorLines);
    mg.getInstructionList().update();
    mg.update();
    mg.getInstructionList().setPositions();
  }

  private int getCurrentPositionInMethod(int i) {
    for (int j = i; j >= 0; j--) {
      final BytecodeLineController bcl =
        (BytecodeLineController)my_editor_lines.get(j);
      if (bcl instanceof InstructionLineController) {
        return bcl.getNoInMethod();
      } else if (bcl instanceof HeaderLineController) {
        return 0;
      }
    }
    return 0;
  }

  /**
   * @param a_start_rem
   * @param an_end_rem
   * @return
   * @throws UmbraException
   */
  private MethodGen getCurrentMethodGen(final int a_start_rem,
                                        final int an_end_rem)
      throws UmbraException {
    MethodGen mg = null;
    if (a_start_rem < an_end_rem) {
      mg = ((InstructionLineController)my_editor_lines.get(a_start_rem)).
           getMethod();
    } else {
      final InstructionLineController il = getInstructionLineAround(
                                                   my_editor_lines,
                                                   a_start_rem);
      if (il != null) {
        mg = il.getMethod();
      } else {
        throw new UmbraException();
      }
    }
    return mg;
  }

  private InstructionLineController getInstructionLineAround(
                        LinkedList the_editor_lines, int pos) {
    int i = pos;
    while (the_editor_lines.get(i) instanceof EmptyLineController ||
           the_editor_lines.get(i) instanceof AnnotationLineController ||
           the_editor_lines.get(i) instanceof CommentLineController) {
      i++;
    }
    final Object o = the_editor_lines.get(i);
    if (o instanceof InstructionLineController) {
      return (InstructionLineController)o;
    }
    return null;
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
      final String lineName = InitParser.removeCommentFromLine(line);
      final String comment = InitParser.extractCommentFromLine(line, a_context);
      final BytecodeLineController lc = Preparsing.getType(lineName, a_context);
      lc.setMethodNo(((BytecodeLineController)my_editor_lines.get(a_j)).
                                                           getMethodNo());
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
   * (they satisfy some syntax conditions). The method inspects all the
   * lines in the given area as represented in the internal structures
   * and checks the correctness of their content. In case a line is not
   * correct, it is added to the structure of incorrect lines.
   *
   * @param a_start the first line number of the area
   * @param an_end the last line number of the area
   * @return <code>true</code> if all lines of the area are correct,
   *   <code>false</code> otherwise
   */
  public boolean checkAllLines(final int a_start,
                               final int an_end)
  {
    boolean ok = true;
    for (int i = a_start; i <= an_end; i++) {
      final BytecodeLineController line =
                               (BytecodeLineController)(my_editor_lines.get(i));
      if (!line.correct()) {
        if (UmbraHelper.DEBUG_MODE) {
          UmbraPlugin.messagelog("checkAllLines:incorrect line=" +
                                 line.getLineContent());
        }
        ok = false;
        my_incorrect.addLast(my_editor_lines.get(i));
      }
    }
    return ok;
  }

  /**
   * @return <code>true</code> if there is no incorrect line within the whole
   *         document
   */
  public boolean allCorrect() {
    return my_incorrect.isEmpty();
  }

  /**
   * @return number of a line that the first error occurs
   * (not necessarily: number of the first line that an error occurs)
   */
  public int getFirstError() {
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
   *     instruction in {@link #my_instructions} array that is the last
   *     instruction in a method or is a non-instruction one located after the
   *     method
   */
  private boolean isEnd(final int a_linenum) {
    final int off = getInstructionOff(a_linenum);
    if (off + 1 >= my_instructions.size()) return true;
    if (off == -1) return false;
    final int index1 = ((BytecodeLineController)my_instructions.get(off)).
                                                             getMethodNo();
    final int index2 = ((BytecodeLineController)my_instructions.get(off + 1)).
             getMethodNo();
    return (index1 != index2);
  }

  /**
   * @param a_linenum a number of a line (including all lines)
   * @return <code>true</code> if the line is located before the first
   *         instruction in a method TODO any method or a fixed method?
   */
  private boolean isFirst(final int a_linenum) {
    final int off = getInstructionOff(a_linenum);
    if (off == 0) return true;
    final int index1 = ((BytecodeLineController)my_instructions.get(off)).
                                                             getMethodNo();
    final int index2 = ((BytecodeLineController)my_instructions.get(off - 1)).
                                                             getMethodNo();
    return (index1 != index2);
  }

  /**
   * TODO.
   * @return TODO
   */
  public boolean[] getModified() {
    return my_modified;
  }

  /**
   * @param the_modified the array that indicates which methods were modified
   */
  public void setModified(final boolean[] the_modified) {
    this.my_modified = the_modified;
  }

  /**
   * Transforms a map from lines to my_comments into string array.
   * TODO
   * @return Array of my_comments
   */
  public String[] getComments() {
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
  public String[] getInterline() {
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

  /**
   * This method handles the initial parsing of a byte code textual document.
   * It creates a parser {@link InitParser} and runs it with the given
   * document and array with comments pertinent to the instruction lines.
   * Subsequently, it initialises the internal structures to handle editor
   * lines, instructions, comments, and modifications.
   *
   * @param a_doc the byte code document with the corresponding BCEL
   *   structures linked into it
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the document,
   *   if this parameter is null then the array is not taken into account
   */
  public void init(final BytecodeDocument a_doc,
                   final String[] a_comment_array) {
    final InitParser initParser = new InitParser(a_doc, a_comment_array);
    initParser.runParsing();
    my_editor_lines = initParser.getEditorLines();
    my_instructions = initParser.getInstructions();
    my_comments = initParser.getComments();
    int a_methodnum = 0;
    if (!my_instructions.isEmpty()) {
      a_methodnum = ((BytecodeLineController)my_instructions.getLast()).
                  getMethodNo() + 1;
    }
    my_modified = new boolean[a_methodnum];
    for (int a_method_count = 0; a_method_count < my_modified.length;
         a_method_count++)
      my_modified[a_method_count] = false;
    if (UmbraHelper.DEBUG_MODE) controlPrint(0);
  }

}
