/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.LinkedList;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.MethodGen;
import annot.bcclass.BCConstantPool;

import umbra.UmbraPlugin;
import umbra.editor.BytecodeDocument;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CPHeaderController;
import umbra.instructions.ast.CPLineController;
import umbra.instructions.ast.ClassHeaderLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.FieldLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.MultiInstruction;
import umbra.instructions.ast.UnknownLineController;
import umbra.lib.FileNames;
import umbra.lib.UmbraException;
import umbra.lib.UmbraLocationException;

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
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class BytecodeController extends BytecodeControllerInstructions {

  /**
   * The constructor which initialises all the internal containers to be
   * empty.
   */
  public BytecodeController() {
    super();

  }

  /**
   * The method finds out which parsing context is appropriate for the given
   * position. It walks back through the structure of the editor lines until
   * a method header is found (and in this case the context is the one
   * appropriate for the method body) or an annotation line (and in this case
   * the context is the one appropriate for annotation).
   *
   * @param a_pos a position to check the context for
   * @return the context for the given position
   */
  private LineContext establishCurrentContext(final int a_pos) {
    final LineContext ctxt = new LineContext();
    for (int i = a_pos; i >= 0;) {
      final BytecodeLineController blc = getLineController(i);
      if (blc instanceof CPHeaderController) {
        ctxt.setInsideCP();
        break;
      }
      if (checkMethodContext(blc, ctxt)) break;
      if (blc instanceof ClassHeaderLineController) {
        ctxt.setInvariantArea();
        break;
      }
      if (blc instanceof AnnotationLineController) {
        ctxt.setInsideAnnotation(getAnnotationEnd(i));
        ctxt.setMethodNo(blc.getMethodNo());
        break;
      }
      if (blc instanceof FieldLineController) {
        ctxt.setFieldArea();
        break;
      }
      /* NOTE (to236111) CPLineController added */
      if (blc instanceof EmptyLineController ||
          blc instanceof InstructionLineController ||
          blc instanceof CommentLineController ||
          blc instanceof UnknownLineController ||
          blc instanceof CPLineController) {
        i--;
      } else {
        break;
      }
    }
    return ctxt;
  }

  /**
   * This methods checks if the given line controller is a witness for
   * the fact that processing is inside a method. In case the processing
   * is inside a method, the method number is established and the
   * context for the processing inside method and the method number are set
   * The method assumes that given line context is in the initial state.
   *
   * @param a_lc the line controller to check
   * @param a_ctxt the context to be set in case the processing is within a
   *   method
   * @return <code>true</code> in case the processing is within a method,
   *   <code>false</code> otherwise
   */
  private boolean checkMethodContext(final BytecodeLineController a_lc,
                                     final LineContext a_ctxt) {
    if (a_lc instanceof HeaderLineController) {
      final int mno = a_lc.getMethodNo();
      if (mno >= 0) {
        a_ctxt.setInsideMethod();
        a_ctxt.setMethodNo(a_lc.getMethodNo());
      }
      return true;
    }
    return false;
  }

  /**
   * The method rearranges the internal representation of the byte code
   * document to take into account the given change in the document.
   *
   * This method parses the given range of the document (between
   * {@code a_start_rem} and {@code a_stop}) and updates the local
   * representation of instructions, comments, and editor lines with the
   * structures resulting from the parsing. This update means that the
   * values for the replaced or removed lines are also removed.
   *
   * @param a_doc a byte code document in which the modification has
   *   been made
   * @param a_start_rem a number of the first modified line as counted in the
   *   old version of the document
   * @param an_end_rem a number of the last modified line as counted in the
   *   old version of the document
   * @param a_stop a number of the last modified line as counted in the new
   *   version of the document
   * @throws UmbraException in case the change cannot be incorporated
   *   into the internal structures
   * @throws UmbraLocationException thrown in case a position has been reached
   *   which is outside the current document
   */
  public void addAllLines(final BytecodeDocument a_doc,
              final int a_start_rem, final int an_end_rem, final int a_stop)
    throws UmbraException, UmbraLocationException {
    final int methodno = getMethodForLine(a_start_rem); // NOTE (to236111) rem == -1 for no a method
    final FragmentParser fgmparser = new FragmentParser(
      (BytecodeDocument)a_doc, a_start_rem, a_stop, methodno);
    final LineContext ctxt = establishCurrentContext(a_start_rem); // NOTE (to236111) ctxt for CP
    fgmparser.runParsing(ctxt);
                            // after that I must know all the instructions are
                            //correct
    final LineContext ctxtold = establishCurrentContext(a_start_rem);
    if (ctxtold.isInsideConstantPool()) {
      doSpecialHandlingForCP();
    } else if (ctxtold.isInInvariantArea()) {
      doSpecialHandlingForInvariants();
    } else if (ctxtold.isInsideAnnotation()) {
      doSpecialHandlingForAnnotations();
    } else if (ctxtold.isInsideMethod()) {
      doSpecialHandlingForMethodBody(a_start_rem, an_end_rem, methodno,
                                     fgmparser);
    }
    updateComments(a_start_rem, an_end_rem, a_stop, fgmparser.getComments());
    updateEditorLines(a_start_rem, an_end_rem, a_stop,
                      fgmparser.getEditorLines(), ctxtold, a_doc);
    if (Preparsing.PARSE_CP && Preparsing.UPDATE_CP) updateBMLCPRepresentation(a_doc);
    if (FileNames.DEBUG_MODE) controlPrint(1);
    if (FileNames.CP_DEBUG_MODE) controlPrintCP(a_doc);
  }
  
  /**
   * Propagates the change in textual representation of constant pool into
   * its BML representation.
   * 
   * TODO (to236111) incremental change
   * 
   * @param a_doc a document in which change happened
   */
  private void updateBMLCPRepresentation(BytecodeDocument a_doc) {
    BCConstantPool bcp = a_doc.getBmlp().getBcc().getCp();
    bcp.clearConstantPool();
    for (int i = 0; i < a_doc.getNumberOfLines(); i++) {
      if (getLineController(i) instanceof CPLineController) {
        CPLineController cplc = (CPLineController) getLineController(i);
        bcp.addConstant(cplc.getConstant(), false);
      }
    }
  }
  
  /**
   * The method performs the special handling for areas which contain constant
   * pools. Currently, it does nothing.
   * 
   * NOTE (to236111) unnecessary because of updateBMLCPRepresentation()?
   */
  private void doSpecialHandlingForCP() {
  }

  /**
   * The method performs the special handling for areas which contain method
   * bodies. It marks the method as edited, removes the LineNumberTable
   * attribute for the method, replaces the instructions in the range
   * <code>a_start_rem</code>-<code>an_end_rem</code> with the instructions
   * from the parser. At last, it updates the labels of the instruction
   * positions in the BCEL byte code representation.
   *
   * @param a_start_rem the first instruction to replace
   * @param an_end_rem the last instruction to replace
   * @param a_methodno the number of the handled method
   * @param a_parser the parser with parsed new content
   * @throws UmbraException the BCEL method representation cannot be retrieved
   */
  private void doSpecialHandlingForMethodBody(final int a_start_rem,
                                              final int an_end_rem,
                                              final int a_methodno,
                                              final FragmentParser a_parser)
    throws UmbraException {
    final MethodGen mg = getCurrentMethodGen(a_start_rem, an_end_rem);
    markModified(a_methodno);
    mg.removeLineNumbers();
    replaceInstructions(a_start_rem, an_end_rem, a_parser.getInstructions());
    mg.getInstructionList().setPositions();
  }

  /**
   * The method performs the special handling for areas which contain BML
   * annotations. Currently, it does nothing.
   */
  private void doSpecialHandlingForAnnotations() {
  }

  /**
   * The method performs the special handling for areas which contain BML
   * invarinats. Currently, it does nothing.
   */
  private void doSpecialHandlingForInvariants() {
  }

  /**
   * Returns the method in which the given line is located.
   *
   * @param a_lineno a line number to find the method for
   * @return the number of the method in which the line is located
   */
  public int getMethodForLine(final int a_lineno) {
    return (getLineController(a_lineno)).getMethodNo();
  }

  /**
   * This method updates the current representation of the editor lines so
   * that the lines in the given area are replaced with the lines from the
   * given list. The lines in the region between <code>a_start_rem</code>
   * and the lower of <code>an_end_rem</code> and <code>a_stop</code> are
   * replaced with the new ones. In case, <code>an_end_rem &lt; a_stop</code>
   * the remaining lines in the given list are added to the current
   * representation of editor lines. In case <code>an_end_rem &gt; a_stop</code>
   * the excessive lines in the current representation are removed. At last,
   * we notify all the listeners in the BCEL structures and we recalculate
   * the positions in the BCEL instruction list.
   *
   * We assume that the given list contains at least
   * <code>a_stop - a_start_rem + 1</code> elements.
   *
   * @param a_start_rem the first line to be updated
   * @param an_end_rem the last line in the old structure to be updated
   * @param a_stop the last line in the new structure
   * @param the_lines the list with the lines to incorporate
   * @param a_ctxt a line context for the updated region
   * @param a_doc a byte code document in which the modification has been made
   * @throws UmbraException in case the BCEL structure that represents
   *   the current method cannot be retrieved or the association between
   *   the BCEL structures and editor lines cannot be removed or the
   *   structure of the editor lines is malformed
   */
  private void updateEditorLines(final int a_start_rem,
                                 final int an_end_rem,
                                 final int a_stop,
                                 final LinkedList the_lines,
                                 final LineContext a_ctxt,
                                 final BytecodeDocument a_doc)
    throws UmbraException {
    if (the_lines.isEmpty()) return; //in case edit should not change anything
    final MethodGen mg = getCurrentMethodGen(a_start_rem, an_end_rem);
    final int j = replaceEditorLines(a_start_rem, an_end_rem, a_stop,
                                     the_lines);
    if (an_end_rem < a_stop) { //we must add the new lines
      addEditorLines(an_end_rem + 1, a_stop, the_lines, j, mg);
    } else if (an_end_rem > a_stop) { //we must remove the deleted lines
      removeEditorLines(an_end_rem, a_stop);
    }
    //my_editor_lines.addAll(a_start_rem, the_lines);
    /* NOTE (to236111) isInsideConstantPool() added */
    if (!a_ctxt.isInsideAnnotation() && !a_ctxt.isInInvariantArea() &&
        !a_ctxt.isInFieldsArea() && !a_ctxt.isInsideConstantPool()) {
      mg.getInstructionList().update();
      mg.update();
      mg.getInstructionList().setPositions();
    }
  }

  /**
   * This method adds to the internal structures the lines of the region from
   * {@code a_start} to {@code a_stop} inclusively. The
   * {@link BytecodeLineController} structures that correspond to the lines
   * are located in the given list {@code the_lines}. The first such structure
   * which should be added is located at the index {@code an_index}. The method
   * generation object {@link MethodGen} which is responsible for handling
   * the edition operations on the byte code file is located in
   * {@code a_methgen}. The lines may be added outside of any method. This
   * situation holds when <code>a_methgen</code> parameter is <code>null</code>.
   *
   * @param a_start the first line in the document to be added
   * @param a_stop the last line in the document to be added
   * @param the_lines the list of {@link BytecodeLineController} objects to
   *   be added to the internal structures
   * @param an_index the index of the first {@link BytecodeLineController} to be
   *   added
   * @param a_methgen the method generation object to associate with the added
   *   lines
   * @throws UmbraException in case wrong {@link BytecodeLineController} is
   *   met
   */
  private void addEditorLines(final int a_start,
                              final int a_stop,
                              final LinkedList the_lines,
                              final int an_index,
                              final MethodGen a_methgen) throws UmbraException {
    if (FileNames.CP_DEBUG_MODE) System.err.println("[[:: ADD ::]]");
    int j = an_index;
    int pos = 0;
    if (a_methgen != null) {
      pos = getCurrentPositionInMethod(a_start);
      if (pos == BytecodeLineController.WRONG_POSITION_IN_METHOD)
        throw new UmbraException();
    }
    for (int i = a_start; i <= a_stop; i++, j++, pos++) {
      try {
        final InstructionLineController newlc =
          (InstructionLineController)the_lines.get(j);
        if (FileNames.CP_DEBUG_MODE)
          System.err.println("<" + newlc.getLineContent() + ">");
        if (a_methgen == null) throw new ClassCastException();
        newlc.makeHandleForPosition(a_methgen, pos);
        insertEditorLine(i, newlc);
      } catch (ClassCastException e) { //we crossed the method boundary
        final BytecodeLineController bcl =
          (BytecodeLineController)the_lines.get(j);
        if (FileNames.CP_DEBUG_MODE)
          System.err.println("<" + bcl.getLineContent() + ">");
        insertEditorLine(i, bcl);
        bcl.addToBCEL();
      }
    }
  }

  /**
   * This method replaces all the line controllers in the given area with
   * the lines from the given list. The first line of the area is delimited
   * by <code>a_start_rem</code> the last line is the smaller of the
   * values <code>an_end_rem</code> and <code>a_stop</code>. The lines in
   * the internal representation are replaced with the lines from
   * <code>the_lines</code> parameter.
   *
   * @param a_start_rem the beginning of the area
   * @param an_end_rem one possible end of the area
   * @param a_stop another possible end of the area
   * @param the_lines the collection of the new lines to replace with the old
   *   ones
   * @param entry_no counter which counts correct constant pool entries 
   * @param a_ctxt a line context for the updated region
   * @param a_doc a byte code document in which the modification has been made
   * @return the number of the first line in {@code the_lines} that was not
   *   replaced
   * @throws UmbraException in case it is impossible to remove the association
   *   between the line and its BCEL representation or the current method
   *   generation structure cannot be obtained
   */
  private int replaceEditorLines(final int a_start_rem,
                                 final int an_end_rem,
                                 final int a_stop,
                                 final LinkedList the_lines)
    throws UmbraException {
    if (FileNames.CP_DEBUG_MODE) System.err.println("[[:: REPLACE ::]]");
    int j = 0;
    for (int i = a_start_rem; i <= an_end_rem && i <= a_stop; i++, j++) {
      //we replace for the common part
      final BytecodeLineController oldlc = getLineController(i);
      BytecodeLineController newlc =
        (BytecodeLineController)the_lines.get(j);
      if (FileNames.CP_DEBUG_MODE)
        System.err.print("<" + oldlc.getLineContent() + "> with ");
      if (FileNames.CP_DEBUG_MODE)
        System.err.println("<" + newlc.getLineContent() + ">");
      if (oldlc.equals(newlc)) continue;
      /* NOTE (to236111) following ifs essentially means:
       * if (newlc insatnceof InstructionLineController and it may be
       * better for readability of code to point it explicitely.
       */
      if (newlc.needsMg() && oldlc.hasMg()) {
        final InstructionLineController iolc =
          (InstructionLineController) oldlc;
        final InstructionLineController ilc = (InstructionLineController) newlc;
        iolc.replace(ilc);
      } else if (newlc.needsMg()) {
        final InstructionLineController ilc = (InstructionLineController) newlc;
        final MethodGen mg = getCurrentMethodGen(a_start_rem, an_end_rem);
        final int pos = getCurrentPositionInMethod(i);
        if (pos == BytecodeLineController.WRONG_POSITION_IN_METHOD)
          throw new UmbraException();
        ilc.makeHandleForPosition(mg, pos + 1);
      } else if (oldlc.hasMg()) {
        final InstructionLineController iolc =
          (InstructionLineController) oldlc;
        iolc.dispose();
      }
      oldlc.removeFromBCEL();
      newlc.addToBCEL();
      replaceLineController(i, newlc);
    }
    return j;
  }

  /**
   * This method returns the number of the instruction (in its method)
   * corresponding to the given position. The method searches for the first
   * instruction line before the given position. In case the header line
   * controller is met before any line controller, it assumes that the line
   * is associated with the number -1. In case a line controller is met,
   * the number of its instruction in the current method is returned. This
   * method may return {@link BytecodeLineController#WRONG_POSITION_IN_METHOD}
   * in case improper {@link BytecodeLineController} is met.
   *
   * @param a_pos the number of the line in the editor
   * @return instruction number (starting with 0) in the current method
   */
  private int getCurrentPositionInMethod(final int a_pos) {
    for (int j = a_pos; j >= 0; j--) {
      final BytecodeLineController bcl = getLineController(j);
      if (bcl.hasMg()) {
        return bcl.getNoInMethod();
      } else if (bcl instanceof HeaderLineController) {
        return -1;
      }
    }
    return 0;
  }

  /**
   * This method returns the BCEL method structure responsible for the
   * edition within the given range of lines. We try to find the instruction
   * line around the first line in the given range
   * (see {@link #getInstructionLineAround(LinkedList, int)}). In case we
   * succeed, we return the MethodGen structure associated with this line.
   *
   * @param a_start_rem the first line of the edited area
   * @param an_end_rem the last line of the edited area
   * @return the {@link MethodGen} structure which handles the editing of this
   *   area
   * @throws UmbraException the {@link MethodGen} cannot be successfully
   *   obtained
   */
  private MethodGen getCurrentMethodGen(final int a_start_rem,
                                        final int an_end_rem)
    throws UmbraException {
    MethodGen mg = null;
    for (int i = a_start_rem; i >= 0; i--) {
      final BytecodeLineController bcl = getLineController(i);
      if (bcl instanceof HeaderLineController) {
        mg = ((HeaderLineController)bcl).getMethod();
        break;
      }
    }
    return mg;
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
      final BytecodeLineController line = getLineController(i);
      if (!line.correct()) {
        if (FileNames.DEBUG_MODE) {
          UmbraPlugin.messagelog("checkAllLines:incorrect line=" +
                                 line.getLineContent());
        }
        ok = false;
        addIncorrect(getLineController(i));
      }
    }
    return ok;
  }
  
  /**
   * This method changes the "dirty" numbers in BCEL constant pool entries
   * into "clean" ones. The change will be reflected only in BCEL, not in
   * internal Umbra representation. <br> 
   * It changes class name index, super class name index and attribute name index
   * of BCEL JavaClass accordingly. <br> <br>
   * 
   * "Clean" and "dirty" numbers are the constant pool entry numbers and
   * references to other constant pool entries normally represented as #{num}.
   * <br> <br>
   * "Clean" numbers are the numbers of a consistent, correct bytecode file,
   * i.e. the file just loaded from class file. <br>
   * When numbers are "clean", constant
   * pool entries are numbered with consecutive natural numbers, starting from 1, i.e.:
   * <br> <br>
   * 
   * <code>
   * const #1 = Class ... <br>
   * const #2 = Utf8 ... <br>
   * const #3 = String ... <br>
   * const #4 = Utf8 ... <br>
   * </code> <br>
   * 
   * and so on. <br> <br>
   * 
   * "Dirty" numbers are numbers entered by user during editing. If for example
   * user wants to enter new entry between entries #2 and #3, it can be numbered
   * with some other number, providing there is no another constant pool entry
   * with such number, i.e.: <br> <br>
   * 
   * <code>
   * const #1 = Class ... <br>
   * const #2 = Utf8 ... <br>
   * const #75 = Utf8 ... <br>
   * const #3 = String ... <br>
   * const #4 = Utf8 ... <br>
   * </code> <br>
   *
   * In both situations ("clean" and "dirty") references reference to the
   * constant pool entry with a given number, i.e. in "dirty" situation:
   * <br> <br> 
   * 
   * <code>
   * const #1 = Class #3 <br>
   * const #2 = Utf8 "something" <br>
   * const #75 = Utf8 "something other" <br>
   * const #3 = String #4 <br>
   * const #4 = Utf8 "a string" <br>
   * </code> <br>
   * 
   * first entry refers to the const #3, not to the third constant (numbered with
   * #75) and entry const #3 refers to the const #4, no to itself (which is in
   * fourth position). <br> <br>
   * 
   * After calling this method all constan pool entries are renumbered starting
   * from 1, and references change accordingly: <br> <br>
   * 
   * <code>
   * const #1 = Class #4 <br>
   * const #2 = Utf8 "something" <br>
   * const #3 = Utf8 "something other" <br>
   * const #4 = String #5 <br>
   * const #5 = Utf8 "a string" <br>
   * </code> <br> <br>
   * 
   * @param a_jc BCEL representation of java class
   */
  public void recalculateCPNumbers(JavaClass a_jc) {
    if (!Preparsing.PARSE_CP || !Preparsing.UPDATE_CP) return;
    HashMap f = new HashMap();
    /*
     * NOTE (to236111) changing number of those two constants forbidden
     * it's not a bug
     */
    int class_name_index = a_jc.getClassNameIndex();
    int super_class_name_index = a_jc.getSuperclassNameIndex();
    int entry_no = 1;
    if (FileNames.CP_DEBUG_MODE) System.err.println("updating pool entries");
    for (int i = 0; i < getNoOfLines(); i++) {
      BytecodeLineController lc = getLineController(i);
      if (lc instanceof CPLineController) {
        CPLineController cplc = (CPLineController) lc;
        f.put(cplc.getConstantNumber(), entry_no);
        entry_no++;
      }
    }
    if (FileNames.CP_DEBUG_MODE) System.err.println("updating instructions");
    for (int i = 0; i < getNoOfLines(); i++) {
      BytecodeLineController lc = getLineController(i);
      if (lc instanceof CPLineController) {
        CPLineController cplc = (CPLineController) lc;
        cplc.updateReferences(f);
      } else if (lc instanceof MultiInstruction) {
        MultiInstruction mi = (MultiInstruction) lc;
        try {
          int pos = getCurrentPositionInMethod(i);
          if (pos == BytecodeLineController.WRONG_POSITION_IN_METHOD)
            throw new UmbraException();
          mi.updateReferences(f, pos);
        } catch (UmbraException e) {
          // TODO (to236111) exception handling
          e.printStackTrace();
        }
      }
    }
    if (FileNames.CP_DEBUG_MODE) System.err.println("updating attributes");
    for (int i = 0; i < a_jc.getAttributes().length; i++) {
      a_jc.getAttributes()[i].
      setNameIndex((Integer) f.get(a_jc.getAttributes()[i].getNameIndex()));
    }
    if (FileNames.CP_DEBUG_MODE) System.err.println("updating class names");
    a_jc.setClassNameIndex((Integer) f.get(class_name_index));
    a_jc.setSuperclassNameIndex((Integer) f.get(super_class_name_index));
    if (FileNames.CP_DEBUG_MODE) System.err.println("ok");
  }
  
}
