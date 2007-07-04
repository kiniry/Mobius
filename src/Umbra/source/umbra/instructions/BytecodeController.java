/*
 * Created on 2005-05-17
 *
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

import umbra.UmbraPlugin;
import umbra.editor.BytecodeDocument;
import umbra.editor.parsing.BytecodeWhitespaceDetector;
import umbra.editor.parsing.IBytecodeStrings;

/**
 * This class defines some structures related to BCEL as well
 * as to Bytecode Editor contents. They are updated after
 * each Bytecode modification and its modification allow
 * updating BCEL. Especially a list of all lines (on purpose to
 * check corectness) as well as a list of instruction lines
 * to detect when BCEL modification is needed. Additional
 * structures keep the information which method has been
 * modified (in case of combining changes) and what comments
 * are added to Bytecode
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeController {

  /**
   * The list of all the lines in the current bytecode editor. These lines
   * are stored as objects the classes of which are subclasses of
   * {@ref BytecodeLineController}.
   */
  private LinkedList all;

  /**
   * The list of all the lines in the editor which contain codes of
   * instructions. These are represented as objects the classes of which
   * are subclasses of {@ref InstructionLineController}.
   */
  private LinkedList instructions;

  /**
   * The list of all the lines which were detected to be incorrect.
   */
  private LinkedList incorrect;

  /**
   * TODO
   */
  private Hashtable comments;

  /**
   * TODO
   */
  private Hashtable interline;

  /**
   * Keeps track of modified methods.
   * TODO is that true?
   */
  private boolean[] modified;

  /**
   * TODO
   */
  public BytecodeController() {
    super();
    all = new LinkedList();
    instructions = new LinkedList();
    incorrect = new LinkedList();
    comments = new Hashtable();
    interline = new Hashtable();
  }

  /**
   * This is a debugging method. It prints out to the standard output the
   * list of all the instructions in the controller.
   */
  public final void showInstructionList() {
    for (int i = 0; i < all.size(); i++) {
      UmbraPlugin.LOG.print(
                  ((BytecodeLineController)(all.get(i))).my_line_text);
    }
  }

  /**
   * This method prints out to the standard output the
   * list of all the incorrect instructions in the controller.
   */
  public final void showAllIncorrectLines()
  {
    UmbraPlugin.messagelog("" + incorrect.size() + " incorrects:");
    UmbraPlugin.LOG.flush();
    for (int i = 0; i < incorrect.size(); i++) {
      UmbraPlugin.messagelog(" " +
             ((BytecodeLineController)(incorrect.get(i))).my_line_text);
    }
  }

  /**
   * Initialization of all the bytecode structures related to
   * the document; it uses BCEL objects associated with the
   * document and based on them it generates the Umbra line
   * structures (subclasses of the {@ref BytecodeLineController})
   * together with the links to the BCEL objects
   *
   * @param a_doc the bytecode document with the corresponding BCEL
   *   structures linked into it
   */
  public final void init(final IDocument a_doc) {
    final ClassGen cg = ((BytecodeDocument)a_doc).getClassGen();
    final ConstantPoolGen cpg = cg.getConstantPool();
    final Method[] methods = cg.getMethods();
    String part_comment = "";
    boolean met_end = true;
    MethodGen mg = null;
    InstructionList il = null;
    InstructionHandle ih = null;
    InstructionHandle end = null;
    int ic = 0; // counts lines with instructions
    // i - iterates over methods
    // j - iterates over lines in the document
    for (int i = 0, j = 0; j < a_doc.getNumberOfLines() - 1; j++) {
      if (met_end && i < methods.length) {
        mg = new MethodGen(methods[i], cg.getClassName(), cpg);
        il = mg.getInstructionList();
        UmbraPlugin.messagelog("method number[" + i + "]" + mg.getName() +
                           "il=" + il.toString());
        ih = il.getStart();
        end = il.getEnd();
        met_end = false;
        i++;
      }
      String line = "";
      try {
        line = a_doc.get(a_doc.getLineOffset(j), a_doc.getLineLength(j));
      } catch (BadLocationException e) {
        MessageDialog.openInformation(new Shell(), "Bytecode",
            "The current document has no positions for line " + j);
      }
      final String lineName = removeCommentFromLine(line);
      final String comment = extractCommentFromLine(line);
      final BytecodeLineController lc = getType(lineName);
      all.add(j, lc);
      if (lc.addHandle(ih, il, mg, i - 1)) { //this is an instruction line
        instructions.add(ic, lc);
        if (comment != null) comments.put(lc, comment);
        if (part_comment.compareTo("") != 0) {
          interline.put(lc, part_comment);
          part_comment = "";
        }
        if (ih == end) {
          met_end = true;
        } else {
          ih = ih.getNext();
        }
        ic++;
      } else //this is non-instruction line in the editor
        if (comment != null) part_comment.concat("\n" + comment);
    }

    final int methodNum = ((BytecodeLineController)instructions.getLast()).
                                getIndex() + 1;
    modified = new boolean[methodNum];
    for (int i = 0; i < modified.length; i++) modified[i] = false;
  }

  /**
   * The method removes from the collection of the incorrect lines
   * all the lines which are between <code>start</code> and
   * <code>stop</code>.
   *
   * @param a_start the first line which is checked for removing
   * @param a_stop the last line which is checked for removing
   */
  public final void removeIncorrects(final int a_start, final int a_stop) {
    for (int i = a_start; i <= a_stop; i++) {
      final BytecodeLineController line = (BytecodeLineController)all.get(i);
      if (incorrect.contains(line)) {
        incorrect.remove(line);
      }
    }
  }

  /**
   * The method detects which kind of modification (adding lines,
   * removing lines or both) has been made and preforms appropriate action
   * to the bytecode structures of the given bytecode document.
   *
   * @param doc a bytecode document in which the modification have
   *      been made to
   * @param startRem  Old-version number of the first modified line
   * @param stopRem  Old-version number of the last modified line
   * @param stop    New-version number of the last modified line
   */
  public final void addAllLines(final IDocument doc,
              final int startRem, final int stopRem, final int stop)
  {
    final ClassGen cg = ((BytecodeDocument)doc).getClassGen();
    UmbraPlugin.messagelog("startRem=" + startRem);
    UmbraPlugin.messagelog("stopRem=" + stopRem);
    UmbraPlugin.messagelog("stop=" + stop);
    // i - index in the removed lines
    // j - index in the inserted lines
    for (int i = startRem, j = startRem;
         (i <= stopRem || j <= stop) && i < all.size();
         i++, j++) {
      final BytecodeLineController oldlc = (BytecodeLineController)all.get(j);
      BytecodeLineController nextLine = null;
      final int off = getInstructionOff(j);
      boolean theLast = false;
      final boolean metEnd = (isEnd(j)) &&
               (oldlc.getIndex() ==
                ((InstructionLineController)instructions.
                             get(off)).getIndex());
      if (metEnd) {
        if (isFirst(j)) {
          theLast = true;
          nextLine = (BytecodeLineController)instructions.get(off);
        } else nextLine = (BytecodeLineController)instructions.get(off - 1);
      } else //TODO poprawnie: 1 enter przed wpisaniem 2 wpisac przed ta przed ktora checmy wstawic i enter; zle inaczej: enter przed i potem wpisac
        nextLine = (BytecodeLineController)instructions.get(off + 1);
      modified[nextLine.getIndex()] = true;
      if (startRem <= j && j <= stop) { //we are in the area of inserted lines
        i = addInstructions(doc, startRem, stopRem, i, j, oldlc,
                  nextLine, theLast, metEnd);
      } else { // we are beyond the area of the inserted instructions
        if (startRem <= i && i <= stopRem) {
          oldlc.dispose(nextLine, cg, theLast, instructions, off);
          all.remove(oldlc);
          j--;
        }
      }
    }
    controlPrint(1);
    return;
  }

  /**
   * TODO
   *
   * @param a_doc bytecode document for which the changes are analysed
   * @param a_start_of_rem the beginning of the removed area
   * @param an_end_rem the end of the removed area
   * @param i TODO
   * @param j TODO
   * @param an_old_lc TODO
   * @param the_next_line TODO
   * @param the_last_flag TODO
   * @param the_methend_flag true when <code>j</code> is the last instruction in a
   *         method
   * @return TODO
   */
  private int addInstructions(final IDocument a_doc,
                              final int a_start_of_rem,
                              final int an_end_rem,
                              final int i,
                              final int j,
                              final BytecodeLineController an_old_lc,
                              final BytecodeLineController the_next_line,
                              final boolean the_last_flag,
                              final boolean the_methend_flag) {
    int res = i;
    final ClassGen cg = ((BytecodeDocument)a_doc).getClassGen();
    final int off = getInstructionOff(j);
    try {
      final String line = a_doc.get(a_doc.getLineOffset(j), a_doc.getLineLength(j));
      //%%
      final String lineName = removeCommentFromLine(line);
      final String comment = extractCommentFromLine(line);
      final BytecodeLineController lc = getType(lineName);
      lc.setIndex(((BytecodeLineController)all.get(j - 1)).getIndex());
      if (comment != null) comments.put(lc, comment);
      final Instruction ins = lc.getInstruction();
      if (ins != null) {
        lc.setTarget(the_next_line.getList(), ins);
      } else {
        if (comment != null) interline.put(the_next_line, comment);
      }
      //UmbraPlugin.messagelog("After target");
      if (res >= a_start_of_rem && res <= an_end_rem) {
        lc.update(an_old_lc, the_next_line, cg, ins, the_methend_flag,
                  the_last_flag, instructions, off);
        all.set(j, lc);
      } else {
        if (an_old_lc.getHandle() == null)
          lc.initHandle(the_next_line, cg, ins, the_methend_flag,
                        instructions, off);
        else
          lc.initHandle(an_old_lc, cg, ins, the_methend_flag,
                        instructions, off);
        all.add(j, lc);
        res--;
      }
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
    return res;
  }

  /**
   * Checks whether all lines of a selected area are correct
   * (they satisfies some given syntax conditions)
   *
   * @param a_start  the beginning of the area
   * @param an_end  the end of the area
   * @return     true if all lines of the area are correct,
   *   false otherwise
   */
  public final boolean checkAllLines(final int a_start,
                                     final int an_end)
  {
    boolean ok = true;
    for (int i = a_start; i <= an_end; i++) {
      final BytecodeLineController line = (BytecodeLineController)(all.get(i));
      if (!line.correct()) {
        ok = false;
        incorrect.addLast(all.get(i));
      }
    }
    return ok;
  }

  /**
   * Chooses one of line types that matches the given line
   * contents
   *
   * @param line  String contents of inserted or modified line
   * @return    Instance of subclass of line controller
   *     that contents of the given line satisfies
   *     classification conditions (Unknown if it does not for all)
   */
  private BytecodeLineController getType(final String line)
  {
    int i;
    boolean ok;
    int j;
    final String l = removeWhiteSpace(removeColonFromLine(line));
    if (l.length() == 0)
      return new EmptyLineController(line);

    //kod - tylko zaczynajace sie Code reszte przy poprawnosci
    if (l.startsWith("Code") ||
       (l.startsWith("LocalVariable")) ||
       (l.startsWith("LineNumber")) ||
       (l.startsWith("Attribute")))
        return new CodeLineController(line);

    //wyjatki throw Exception from nie znam reguly
    if ((l.startsWith("throws")) ||
      (l.startsWith("Exception")) ||
      (l.startsWith("From")))
      return new ThrowsLineController(line);

    //naglowki - public static void private
    // i na wszelki wypadek - int char protected boolean String byte
    if ((l.startsWith("public")) || (l.startsWith("static")) ||
      (l.startsWith("void")) || (l.startsWith("private")) ||
      (l.startsWith("int")) || (l.startsWith("char")) ||
      (l.startsWith("protected")) || (l.startsWith("boolean")) ||
      (l.startsWith("String")) || (l.startsWith("byte")) ||
      (l.startsWith("package")) || (l.startsWith("class")) ||
      (l.startsWith("}")))
      return new HeaderLineController(line);

    if ((l.startsWith("*")) || (l.startsWith("/*")))
      return new AnnotationLineController(line);


    //instrukcje liczba i :
    // a potem w zaleznosci od rodzaju

    final int ppos = line.indexOf(":");
    if (ppos >= 0) { //nie >= czy jest : od 2 pozycji
      //tzn liczy chyba od zerowej czyli sprawdzaczy cyfra przed
      //UmbraPlugin.messagelog("dwukropek" + ppos + line.charAt(0) + line.charAt(1));
      ok = true;
      for (i = 0; i < ppos; i++) {
        //UmbraPlugin.messagelog("i" + i + line.charAt(i) + line.charAt(1));
        //sprawdza czy tylko numeryczne przed :
        if  (!(Character.isDigit(line.charAt(i)))) ok = false;
      }
      String subline = line.substring(ppos + 1);
      while (Character.isWhitespace(subline.charAt(0))) subline = subline.substring(1);
      for (i = 1; i < subline.length(); i++) {
        if (Character.isWhitespace(subline.charAt(i))) {
          subline = subline.substring(0, i);
          break;
        }
      }
      if (ok) {
        final String[] s1 = IBytecodeStrings.single;
        final String[] s2 = IBytecodeStrings.push;
        final String[] s3 = IBytecodeStrings.jump;
        final String[] s4 = IBytecodeStrings.incc;
        final String[] s5 = IBytecodeStrings.stack;
        final String[] s6 = IBytecodeStrings.array;
        final String[] s7 = IBytecodeStrings.anew;
        final String[] s8 = IBytecodeStrings.field;
        final String[] s9 = IBytecodeStrings.invoke;
        final String[] s10 = IBytecodeStrings.ldc;
        final String[] s11 = IBytecodeStrings.unknown;
        //wazna jest kolejnosc bo aload_0 przed aload
        // i ty tworzenie inshan !!!!!!!!!
        for (j = 0; j < s1.length; j++) {
          if (subline.equalsIgnoreCase(s1[j]))
            return new SingleInstruction(line, s1[j]);
        }
        for (j = 0; j < s2.length; j++) {
          if (subline.equalsIgnoreCase(s2[j]))
            return new PushInstruction(line, s2[j]);
        }
        for (j = 0; j < s3.length; j++) {
          if (subline.equalsIgnoreCase(s3[j]))
            return new JumpInstruction(line, s3[j]);
        }
        for (j = 0; j < s4.length; j++) {
          if (subline.equalsIgnoreCase(s4[j]))
            return new IncInstruction(line, s4[j]);
        }
        for (j = 0; j < s5.length; j++) {
          if (subline.equalsIgnoreCase(s5[j]))
            return new StackInstruction(line, s5[j]);
        }
        for (j = 0; j < s6.length; j++) {
          if (subline.equalsIgnoreCase(s6[j]))
            return new ArrayInstruction(line, s6[j]);
        }
        for (j = 0; j < s7.length; j++) {
          if (subline.equalsIgnoreCase(s7[j]))
            return new NewInstruction(line, s7[j]);
        }
        for (j = 0; j < s8.length; j++) {
          if (subline.equalsIgnoreCase(s8[j]))
            return new FieldInstruction(line, s8[j]);
        }
        for (j = 0; j < s9.length; j++) {
          if (subline.equalsIgnoreCase(s9[j]))
            return new InvokeInstruction(line, s9[j]);
        }
        for (j = 0; j < s10.length; j++) {
          if (subline.equalsIgnoreCase(s10[j]))
            return new LdcInstruction(line, s10[j]);
        }
        for (j = 0; j < s11.length; j++) {
          if (subline.equalsIgnoreCase(s11[j]))
            return new UnknownInstruction(line, s11[j]);
        }
      }
    }

    //String[] s = IBytecodeStrings.instructions;
    //for (int i = 0; i < s.length; i++) {
    //  if ((l.startsWith(s[i] + " ")) || (l.equalsIgnoreCase(s[i])))
    //    return new InstructionLineController(line);
    //}
    return new UnknownLineController(line);
  }

  /**
   * This method strips off the whitespace characters both at the beginning
   * and at the end of the given string.
   *
   * @param string to strip off the whitespace
   * @return the string with no whitespace
   */
  private String removeWhiteSpace(/*@ non_null @*/ final String string) {
    final BytecodeWhitespaceDetector wd = new BytecodeWhitespaceDetector();
    int i = 0;
    boolean ok = true;
    while (ok && i < string.length() && string.length() > 0) {
      if (!wd.isWhitespace(string.charAt(i))) ok = false;
      i++;
    }
    if (ok) return "";
    int j = string.length() - 1;
    ok = true;
    while (ok && j >= 0) {
      if (!wd.isWhitespace(string.charAt(j))) ok = false;
      j--;
    }
    if (ok) return "";
    return string.substring(i - 1, j + 2);
  }

  /**
   * Removes an one-line comment from line of bytecode.
   *
   * @param a_line  line of bytecode
   * @return  bytecode line l without one-line comment and ending whitespaces
   */
  protected final String removeCommentFromLine(final String a_line) {
    String res;
    int j = a_line.length() - 1;

    final int k = (a_line.indexOf("//", 0));
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
   * @param l the string to strip the initial characters from
   */
  protected final String removeColonFromLine(final String l) {
    int i = 0;
    while ((i < l.length()) && (Character.isDigit(l.charAt(i))))
      i++;
    if ((i < l.length()) && (l.charAt(i) == ':'))
      i++;
    while ((i < l.length()) && (Character.isWhitespace(l.charAt(i))))
      i++;
    return l.substring(i, l.length());
  }

  /**
   * The method checks if the given line contains a single line comment
   * and extracts the comment string. In case there is no
   * comment in the line, it returns <code>null</code>.
   *
   * @param line  the line to check for comments
   * @return    comment or null
   */
  private String extractCommentFromLine(final String line) {
    final int i = line.indexOf("//");
    if (i == -1) return null;
    final String nl = line.substring(i + 2, line.indexOf("\n"));
    UmbraPlugin.messagelog("//" + nl);
    return nl;
  }

  /**
   * @return true if there is no incorrect line within the whole document
   */
  public final boolean allCorrect() {
    return incorrect.isEmpty();
  }

  /**
   * @return Number of a line that the first error occurs
   * (not necessarily: number of the first line that an error occurs)
   */
  public final int getFirstError() {
    return all.lastIndexOf(incorrect.getFirst());
  }

  /**
   * The method finds index in the instruction array that is linked with
   * the position in the line array
   *
   * @param lineNum line number (including all lines in a document)
   * @return  Instruction offset (including only instruction lines)
   *   or -1 if the line is not an instruction
   */
  private int getInstructionOff(final int lineNum) {
    for (int i = lineNum; i >= 0; i--) {
      final Object line = all.get(i);
      if (instructions.contains(line))
        return instructions.indexOf(line);
    }
    return -1;
  }

  /**
   * @param lineNum numebr of line (including all lines in the textual
   *    representation)
   * @return true if the <code>lineNum</code> is a number of an instruction
   *     in <code>instructions</code> array that is the last instruction
   *     in a method or is a non-istruction one located after the method
   */
  private boolean isEnd(final int lineNum) {
    final int off = getInstructionOff(lineNum);
    if (off + 1 >= instructions.size()) return true;
    if (off == -1) return false;
    final int index1 = ((BytecodeLineController)instructions.get(off)).getIndex();
    final int index2 = ((BytecodeLineController)instructions.get(off + 1)).
             getIndex();
    return (index1 != index2);
  }

  /**
   * @param lineNum Numebr of line (including all lines)
   * @return true if the line is located before the first instruction in a method
   */
  private boolean isFirst(final int lineNum) {
    final int off = getInstructionOff(lineNum);
    if (off == 0) return true;
    final int index1 = ((BytecodeLineController)instructions.get(off)).getIndex();
    final int index2 = ((BytecodeLineController)instructions.get(off - 1)).getIndex();
    return (index1 != index2);
  }

  /**
   * TODO
   */
  public final boolean[] getModified() {
    return modified;
  }

  /**
   * TODO
   * @param the_modified
   */
  public final void setModified(final boolean[] the_modified) {
    this.modified = the_modified;
  }

  /**
   * Transforms a map from lines to comments into string array.
   *
   * @return Array of comments
   */
  public final String[] getComments() {
    final String[] commentTab = new String[instructions.size()];
    for (int i = 0; i < instructions.size(); i++) {
      final Object lc = instructions.get(i);
      final String com = (String)comments.get(lc);
      commentTab[i] = com;
    }
    return commentTab;
  }

  /**
   * TODO
   */
  public final String[] getInterline() {
    final String[] commentTab = new String[instructions.size()];
    for (int i = 0; i < instructions.size(); i++) {
      final Object lc = instructions.get(i);
      final String com = (String)interline.get(lc);
      commentTab[i] = com;
    }
    return commentTab;
  }

  /**
   * TODO
   *
   * @param an_index TODO
   */
  private void controlPrint(final int an_index) {
    UmbraPlugin.messagelog("");
    UmbraPlugin.messagelog("Control print of bytecode modification (" + an_index + "):");
    for (int i = 0; i < instructions.size(); i++) {
      final InstructionLineController line = (InstructionLineController)instructions.get(i);
      if (line == null) {
        UmbraPlugin.messagelog("" + i + ". null");
        return;
      }
      //if (line.index == index) {
      UmbraPlugin.messagelog("" + i + ". " + line.name);
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
