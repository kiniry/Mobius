/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.ConstantValue;
import org.apache.bcel.classfile.ExceptionTable;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.PMGClass;
import org.apache.bcel.classfile.Signature;
import org.apache.bcel.classfile.SourceFile;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import annot.bcclass.BCConstantPool;
import annot.bcclass.BCMethod;

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
import umbra.instructions.errors.AttributeNoSuchConstantError;
import umbra.instructions.errors.ClassNameNoSuchConstantError;
import umbra.instructions.errors.ConflictingCPNumbersError;
import umbra.instructions.errors.ErrorReport;
import umbra.instructions.errors.FieldNoSuchConstantError;
import umbra.instructions.errors.MethodNoSuchConstantError;
import umbra.instructions.errors.SuperclassNameNoSuchConstantError;
import umbra.lib.BytecodeStrings;
import umbra.lib.FileNames;
import umbra.lib.UmbraCPRecalculationException;
import umbra.lib.UmbraException;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraNoSuchConstantException;

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
    final ArrayList < BytecodeLineController > old_lines =
      new ArrayList < BytecodeLineController > ();
    final ArrayList < Integer > old_lines_index = new ArrayList < Integer > ();
    int entry_no = 0;
    for (int i = 0; i < getNoOfLines(); i++) {
      old_lines.add(getLineController(i));
      if (getLineController(i) instanceof CPLineController) {
        // TODO (Umbra) does not work with Long and Double
        entry_no++;
        old_lines_index.add(entry_no);
      } else {
        old_lines_index.add(-1);
      }
    }
    final int methodno = getMethodForLine(a_start_rem);
    final FragmentParser fgmparser = new FragmentParser(
      (BytecodeDocument)a_doc, a_start_rem, a_stop, methodno);
    final LineContext ctxt = establishCurrentContext(a_start_rem);
    if (ctxt.isInsideConstantPool() && !getMapping().isCPEditionAllowed())
      throw new UmbraException();
    fgmparser.runParsing(ctxt);
                            // after that I must know all the instructions are
                            //correct
    for (Field f : a_doc.getJavaClass().getFields()) {
      if (!getMapping().containsField(f)) {
        getMapping().setCPEditionAllowed(false);
        break;
      }
    }
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
    if (getMapping().isCPEditionAllowed()) {
      updateBMLCPRepresentation(a_doc, a_start_rem, an_end_rem, a_stop,
                                old_lines, old_lines_index);
      try {
        a_doc.updateBML();
      } catch (umbra.lib.UmbraCPRecalculationException e) {
        e.printStackTrace();
      }
    }
    if (FileNames.DEBUG_MODE) controlPrint(1);
    if (FileNames.CP_DEBUG_MODE) controlPrintCP(a_doc);
    a_doc.setDirty(true);
  }

  /**
   * Propagates the change in textual representation of constant pool into
   * its BML representation. It is called after the change has been propagated
   * into Umbra internal representation (line controllers) <br> <br>
   *
   * TODO (Umbra) what if CPLineController outside constant pool? <br> <br>
   *
   * @param a_doc a document in which change happened
   * @param a_start_rem a number of the first modified line as counted in the
   *   old version of the document
   * @param an_end_rem a number of the last modified line as counted in the
   *   old version of the document
   * @param a_stop a number of the last modified line as counted in the new
   *   version of the document
   * @param an_old_lines lines representing document before change
   * @param an_old_indices an_old_indices.get(i) = k when an_old_lines.get(i)
   *   is CPLineController and it represents a constant that is at position k
   *   in BCEL representation of ConstantPool. If an_old_lines.get(i) isn't
   *   CPLineController, an_old_indices.get(i) = -1.
   */
  private void updateBMLCPRepresentation(final BytecodeDocument a_doc,
                      final int a_start_rem,
                      final int an_end_rem, final int a_stop,
                      final ArrayList < BytecodeLineController > an_old_lines,
                      final ArrayList < Integer > an_old_indices) {
    final BCConstantPool bcp = a_doc.getBmlp().getBcc().getCp();
    int first_before = 0;
    for (int i = a_start_rem - 1; i >= 0; i--) {
      if (an_old_indices.get(i) > -1) {
        first_before = an_old_indices.get(i);
        break;
      }
    }
    for (int i = a_start_rem; i <= an_end_rem; i++) {
      if (an_old_lines.get(i) instanceof CPLineController) {
        final CPLineController cplc = (CPLineController) an_old_lines.get(i);
        if (i <= a_stop && getLineController(i) instanceof CPLineController) {
          bcp.replaceConstant(an_old_indices.get(i),
                              ((CPLineController)
                                  getLineController(i)).getConstant());
          first_before = an_old_indices.get(i);
          if (FileNames.CP_DEBUG_MODE)
            UmbraPlugin.messagelog("REPLACING " + an_old_lines.get(i) +
                                   ", index " +
                             an_old_indices.get(i) + " WITH " +
                             cplc.getConstant() +
                             ", first_before " + first_before);
        } else {
          bcp.justRemoveConstant(an_old_indices.get(i));
          if (FileNames.CP_DEBUG_MODE)
            UmbraPlugin.messagelog("REMOVING " + an_old_lines.get(i) +
                                   ", index " +
                             an_old_indices.get(i) + ", first_before " +
                             first_before);
          for (int j = i + 1; j <= an_end_rem; j++) {
            an_old_indices.set(j, an_old_indices.get(j) - 1);
          }
        }
      } else if (i <= a_stop &&
          getLineController(i) instanceof CPLineController) {
        bcp.addConstantAfter(((CPLineController)
            getLineController(i)).getConstant(),
                             first_before);
        first_before++;
        for (int j = i + 1; j < an_end_rem; j++) {
          an_old_indices.set(j, an_old_indices.get(j) + 1);
        }
        if (FileNames.CP_DEBUG_MODE) UmbraPlugin.messagelog("ADDING " +
                           ((CPLineController)
                               getLineController(i)).getConstant() +
                           ", first_before " + first_before);
      }
    }
    if (an_end_rem < a_stop) {
      for (int i = an_end_rem + 1; i <= a_stop; i++) {
        if (getLineController(i) instanceof CPLineController) {
          final CPLineController cplc = (CPLineController) getLineController(i);
          bcp.addConstantAfter(cplc.getConstant(), first_before);
          first_before++;
          for (int j = i + 1; j < an_end_rem; j++) {
            an_old_indices.set(j, an_old_indices.get(j) + 1);
          }
          if (FileNames.CP_DEBUG_MODE)
            UmbraPlugin.messagelog("ADDING " + cplc.getConstant() +
                             ", first_before " + first_before);
        }
      }
    }
  }

  /**
   * The method performs the special handling for areas which contain constant
   * pools. Currently, it does nothing.
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
    final BCMethod mg = getCurrentMethod(a_start_rem, an_end_rem);
    markModified(a_methodno);
    mg.getBcelMethod().removeLineNumbers();
    replaceInstructions(a_start_rem, an_end_rem, a_parser.getInstructions());
    mg.getInstructions().setPositions();
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
    final BCMethod mg = getCurrentMethod(a_start_rem, an_end_rem);
    final int j = replaceEditorLines(a_start_rem, an_end_rem, a_stop,
                                     the_lines);
    if (an_end_rem < a_stop) { //we must add the new lines
      addEditorLines(an_end_rem + 1, a_stop, the_lines, j, mg);
    } else if (an_end_rem > a_stop) { //we must remove the deleted lines
      removeEditorLines(an_end_rem, a_stop);
    }
    //my_editor_lines.addAll(a_start_rem, the_lines);
    if (!a_ctxt.isInsideAnnotation() && !a_ctxt.isInInvariantArea() &&
        !a_ctxt.isInFieldsArea() && !a_ctxt.isInsideConstantPool()) {
      mg.getInstructions().update();
      mg.getBcelMethod().update();
      mg.getInstructions().setPositions();
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
                              final BCMethod a_methgen) throws UmbraException {
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
      final BytecodeLineController newlc =
        (BytecodeLineController)the_lines.get(j);
      if (FileNames.CP_DEBUG_MODE)
        System.err.print("<" + oldlc.getLineContent() + "> with ");
      if (FileNames.CP_DEBUG_MODE)
        System.err.println("<" + newlc.getLineContent() + ">");
      if (oldlc.equals(newlc)) continue;
      if (newlc.needsMg() && oldlc.hasMg()) {
        final InstructionLineController iolc =
          (InstructionLineController) oldlc;
        final InstructionLineController ilc = (InstructionLineController) newlc;
        iolc.replace(ilc);
      } else if (newlc.needsMg()) {
        final InstructionLineController ilc = (InstructionLineController) newlc;
        final BCMethod mg = getCurrentMethod(a_start_rem, an_end_rem);
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
   * @return the {@link BCMethod} structure which handles the editing of this
   *   area
   * @throws UmbraException the {@link BCMethod} cannot be successfully
   *   obtained
   */
  private BCMethod getCurrentMethod(final int a_start_rem,
                                    final int an_end_rem)
    throws UmbraException {
    BCMethod mg = null;
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
   * It changes class name index, super class name index, attribute name index,
   * field name index and field signature index of BCEL JavaClass accordingly.
   * <br> <br>
   *
   * "Clean" and "dirty" numbers are the constant pool entry numbers and
   * references to other constant pool entries normally represented as #{num}.
   * <br> <br>
   * "Clean" numbers are the numbers of a consistent, correct bytecode file,
   * i.e. the file just loaded from class file. <br>
   * When numbers are "clean", constant
   * pool entries are numbered with consecutive natural numbers,
   * starting from 1, i.e.:
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
   * first entry refers to the const #3, not to the third constant
   * (numbered with #75) and entry const #3 refers to the const #4,
   * no to itself (which is in fourth position). <br> <br>
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
   * @param classGen BCEL representation of java class
   * @throws UmbraCPRecalculationException when errors in bytecode caused
   * recalculation impossible
   */
  public void recalculateCPNumbers(final ClassGen classGen)
    throws UmbraCPRecalculationException {
    int const_no = 0;
    // XXX (Umbra) why is this necessary?
    for (int i = 0; i < getNoOfLines(); i++) {
      if (getLineController(i) instanceof CPLineController) {
        // TODO (Umbra) does not work with Long and Double
        const_no++;
        ((CPLineController)
            getLineController(i)).setConstant(
                                classGen.getConstantPool().getConstant(const_no));
      }
    }
    final HashMap f = new HashMap();
    f.put(-1, classGen.getConstantPool().getSize());
    /*
     * XXX (Umbra) changing the index of those two constants forbidden
     * it's not a bug
     */
    final int class_name_index = getMapping().getClassNameIndex();
    final int super_class_name_index = getMapping().getSuperclassNameIndex();
    int entry_no = 1;
    if (FileNames.CP_DEBUG_MODE) UmbraPlugin.messagelog("creating map");
    for (int i = 0; i < getNoOfLines(); i++) {
      final BytecodeLineController lc = getLineController(i);
      if (lc instanceof CPLineController) {
        final CPLineController cplc = (CPLineController) lc;
        f.put(cplc.getConstantNumber(), entry_no);
        // TODO (Umbra) does not work with Long and Double
        entry_no++;
      }
    }
    if (FileNames.CP_DEBUG_MODE)
      UmbraPlugin.messagelog("updating pool and instructions");
    boolean wasscp = false;
    for (int i = 0; i < getNoOfLines(); i++) {
      final BytecodeLineController lc = getLineController(i);
      if (lc instanceof CPHeaderController &&
          lc.getMy_line_text().
             startsWith(BytecodeStrings.
                        JAVA_KEYWORDS[BytecodeStrings.SCP_KEYWORD_POS])) {
        wasscp = true;
        continue;
      }
      if (lc instanceof CPLineController && !wasscp) {
        final CPLineController cplc = (CPLineController) lc;
        if (FileNames.CP_DEBUG_MODE)
          UmbraPlugin.messagelog(lc.getLineContent());
        cplc.updateReferences(f);
      } else if (lc instanceof MultiInstruction) {
        final MultiInstruction mi = (MultiInstruction) lc;
        if (FileNames.CP_DEBUG_MODE)
          UmbraPlugin.messagelog(lc.getLineContent());
        try {
          final int pos = getCurrentPositionInMethod(i);
          if (pos == BytecodeLineController.WRONG_POSITION_IN_METHOD)
            throw new UmbraException();
          mi.updateReferences(f, pos);
        } catch (UmbraException e) {
          // XXX (Umbra) exception handling
          e.printStackTrace();
        }
      }
    }
    if (FileNames.CP_DEBUG_MODE) UmbraPlugin.messagelog("updating attributes");
    final List < Attribute > attrs = new ArrayList < Attribute > ();
    if (FileNames.CP_DEBUG_MODE) UmbraPlugin.messagelog("updating fields");
    for (int i = 0; i < classGen.getFields().length; i++) {
      classGen.getFields()[i].setNameIndex(
        (Integer) dirtyToClean(f,
                               getMapping().getFieldName(classGen.getFields()[i])));
      classGen.getFields()[i].setSignatureIndex(
        (Integer) dirtyToClean(f,
                          getMapping().getFieldSignature(classGen.getFields()[i])));
      for (Attribute a : classGen.getFields()[i].getAttributes()) attrs.add(a);
    }
    for (int i = 0; i < classGen.getMethods().length; i++) {
      classGen.getMethods()[i].setNameIndex((Integer)
        dirtyToClean(f, getMapping().getMethodName(classGen.getMethods()[i])));
      classGen.getMethods()[i].setSignatureIndex((Integer)
        dirtyToClean(f, getMapping().getMethodSignature(classGen.getMethods()[i])));
      for (Attribute a : classGen.getMethods()[i].getAttributes()) {
        if (a instanceof Code) {
          final Code c = (Code) a;
          for (Attribute at : c.getAttributes()) attrs.add(at);
        }
        attrs.add(a);
      }
    }
    for (Attribute a : classGen.getAttributes()) attrs.add(a);
    recalculateCPNumbersForAttributes(attrs, f);
    /*
     * XXX (Umbra) Local variables (LocalVariable in BCEL) also have
     * references to constant pool (name and signature index). Those
     * references were somehow updated automatically. However, when dummy
     * generation for local variables was added, this had broken and the
     * following code for manual update of local variable references was
     * added:
     */
    final List < LocalVariable > lvars = getMapping().getLocVars(classGen);
    for (LocalVariable lv : lvars) {
      lv.setNameIndex((Integer)
                      dirtyToClean(f, getMapping().getLocVarNameIndex(lv)));
      lv.setSignatureIndex((Integer)
                         dirtyToClean(f, getMapping().getLocVarSignatureIndex(lv)));
    }
    if (FileNames.CP_DEBUG_MODE) UmbraPlugin.messagelog("updating class names");
    classGen.setClassNameIndex((Integer) dirtyToClean(f, class_name_index));
    classGen.setSuperclassNameIndex((Integer)
                                dirtyToClean(f, super_class_name_index));
    if (FileNames.CP_DEBUG_MODE) UmbraPlugin.messagelog("ok");
  }

  /**
   * This method affects references to constant pool entries for attributes
   * in BCEL representation of bytecode. It changes the references from "dirty"
   * to "clean" numbers. <br> <br>
   *
   * TODO (Umbra) PMGClass, Signature and ConstantValue not tested
   *
   * @param an_attrs list of attributes
   * @param a_map mapping from "dirty" to "clean" numbers
   */
  private void recalculateCPNumbersForAttributes(final List < Attribute >
  an_attrs,
                                                 final HashMap a_map) {
    for (Attribute a : an_attrs) {
      a.setNameIndex((Integer) dirtyToClean(a_map,
                                            getMapping().getAttributeName(a)));
      if (a instanceof SourceFile) {
        final SourceFile src = (SourceFile) a;
        src.setSourceFileIndex((Integer)
          dirtyToClean(a_map, getMapping().getAttributeSecondValue(src)));
      } else if (a instanceof ConstantValue) {
        final ConstantValue cv = (ConstantValue) a;
        cv.setConstantValueIndex((Integer)
          dirtyToClean(a_map, getMapping().getAttributeSecondValue(cv)));
      } else if (a instanceof ExceptionTable) {
        final ExceptionTable et = (ExceptionTable) a;
        final int[] exception_table =
          new int[et.getExceptionIndexTable().length];
        for (int i = 0; i < et.getExceptionIndexTable().length; i++) {
          exception_table[i] =
            (Integer) dirtyToClean(a_map,
                                   getMapping().getExceptionTable(et)[i]);
        }
        et.setExceptionIndexTable(exception_table);
      } else if (a instanceof PMGClass) {
        final PMGClass pmgc = (PMGClass) a;
        pmgc.setPMGClassIndex((Integer)
          dirtyToClean(a_map, getMapping().getPMGClass(pmgc)));
        pmgc.setPMGIndex((Integer)
          dirtyToClean(a_map, getMapping().getAttributeSecondValue(pmgc)));
      } else if (a instanceof Signature) {
        final Signature sig = (Signature) a;
        sig.setSignatureIndex((Integer)
          dirtyToClean(a_map, getMapping().getAttributeSecondValue(sig)));
      }
    }
  }

  /**
   * Returns "clean" number for a given "dirty" one. If there is no such
   * "dirty" number (there is no constant with that number in textual bytecode
   * representation) size of constant pool + 1 is returned.
   *
   * @param a_map a map that maps "dirty" numbers onto "clean" ones; the map
   * should contain size of the constant pool at the key -1
   * @param a_num "dirty" number
   * @return "clean" number corresponding to a given "dirty" one
   */
  public int dirtyToClean(final HashMap a_map, final int a_num) {
    if (a_map.containsKey(a_num)) return (Integer) a_map.get(a_num);
    return (Integer) a_map.get(-1) + 1;
  }

  /**
   * Checks if there are any conflicting constant numbers in textual
   * representation of constant pool or are there any references to
   * non-existing constants. <br> <br>
   *
   * TODO (Umbra) also check whether references are to correct CP
   * entries (i.e. if const String references const Utf8 and not
   * const Fieldref; name index of attribute ExceptionTable points to
   * const Utf8 with value "Exception; etc.) <br> <br>
   *
   * TODO (Umbra) also check if there are references to non existing
   * constants from local variables (name and signature index)
   *
   * @param classGen a BCEL representation of bytecode
   * @return error report
   */
  public ErrorReport getErrorReport(final ClassGen classGen) {
    final HashSet < Integer > existing = new HashSet < Integer > ();
    final HashMap conflict = new HashMap();
    final ErrorReport a_report = new ErrorReport();
    if (FileNames.CP_DEBUG_MODE) System.err.println("detecting conflicts");
    for (int i = 0; i < getNoOfLines(); i++) {
      final BytecodeLineController lc = getLineController(i);
      if (lc instanceof CPLineController) {
        final CPLineController cplc = (CPLineController) lc;
        existing.add(cplc.getConstantNumber());
        final int no = cplc.getConstantNumber();
        if (!conflict.containsKey(no)) {
          final ConflictingCPNumbersError an_error =
            new ConflictingCPNumbersError();
          an_error.addLine(cplc);
          conflict.put(no, an_error);
        } else {
          ((ConflictingCPNumbersError) conflict.get(no)).addLine(cplc);
        }
      }
    }
    for (Object o : conflict.values()) {
      final ConflictingCPNumbersError cpne = (ConflictingCPNumbersError) o;
      if (cpne.getCauses().length > 1) a_report.addError(cpne);
    }
    for (int i = 0; i < getNoOfLines(); i++) {
      final BytecodeLineController lc = getLineController(i);
      if (lc instanceof CPLineController) {
        final CPLineController cplc = (CPLineController) lc;
        try {
          cplc.checkCorrectness(existing);
        } catch (UmbraNoSuchConstantException e) {
          a_report.addError(e.getError());
        }
      } else if (lc instanceof MultiInstruction) {
        final MultiInstruction mlc = (MultiInstruction) lc;
        try {
          mlc.checkCorrectness(existing);
        } catch (UmbraNoSuchConstantException e) {
          a_report.addError(e.getError());
        }
      }
    }
    if (!existing.contains(getMapping().getClassNameIndex())) {
      final ClassNameNoSuchConstantError cnnsce =
        new ClassNameNoSuchConstantError(getMapping().getClassNameIndex());
      a_report.addError(cnnsce);
    }
    if (!existing.contains(getMapping().getSuperclassNameIndex())) {
      final SuperclassNameNoSuchConstantError scnnsce =
        new SuperclassNameNoSuchConstantError(getMapping().
                                              getSuperclassNameIndex());
      a_report.addError(scnnsce);
    }
    final List < Attribute > attrs = new ArrayList < Attribute > ();
    for (Field f : classGen.getFields()) {
      for (Attribute a : f.getAttributes()) attrs.add(a);
      if (!existing.contains(getMapping().getFieldName(f))) {
        final FieldNoSuchConstantError fnsce = new FieldNoSuchConstantError();
        fnsce.setField(f);
        fnsce.addNumber(getMapping().getFieldName(f));
        if (!existing.contains(getMapping().getFieldSignature(f))) {
          fnsce.addNumber(getMapping().getFieldSignature(f));
        }
        a_report.addError(fnsce);
      } else if (!existing.contains(getMapping().getFieldSignature(f))) {
        final FieldNoSuchConstantError fnsce = new FieldNoSuchConstantError();
        fnsce.setField(f);
        fnsce.addNumber(getMapping().getFieldSignature(f));
        a_report.addError(fnsce);
      }
    }
    for (Method m : classGen.getMethods()) {
      for (Attribute a : m.getAttributes()) {
        if (a instanceof Code) {
          final Code c = (Code) a;
          for (Attribute at : c.getAttributes()) attrs.add(at);
        }
        attrs.add(a);
      }
      if (!existing.contains(getMapping().getMethodName(m))) {
        final MethodNoSuchConstantError mnsce = new MethodNoSuchConstantError();
        mnsce.setMethod(m);
        mnsce.addNumber(getMapping().getMethodName(m));
        if (!existing.contains(getMapping().getMethodSignature(m))) {
          mnsce.addNumber(getMapping().getMethodSignature(m));
        }
        a_report.addError(mnsce);
      } else if (!existing.contains(getMapping().getMethodSignature(m))) {
        final MethodNoSuchConstantError mnsce = new MethodNoSuchConstantError();
        mnsce.setMethod(m);
        mnsce.addNumber(getMapping().getMethodSignature(m));
        a_report.addError(mnsce);
      }
    }
    for (Attribute a : classGen.getAttributes()) attrs.add(a);
    checkForAttributes(attrs, existing, a_report);
    return a_report;
  }

  /**
   * Checks if there are any references from attributes to
   * constant non-existing in textual representation of constant pool.
   *
   * @param an_attrs list of attributes
   * @param an_existing numbers of existing constants
   * @param a_report error report
   */
  private void checkForAttributes(final List < Attribute > an_attrs,
                                 final HashSet < Integer > an_existing,
                                 final ErrorReport a_report) {
    for (Attribute a : an_attrs) {
      final AttributeNoSuchConstantError ansce =
        new AttributeNoSuchConstantError();
      ansce.setAttribute(a);
      boolean was_error = false;
      if (!an_existing.contains(getMapping().getAttributeName(a))) {
        ansce.addNumber(getMapping().getAttributeName(a));
        was_error = true;
      }
      if (a instanceof SourceFile || a instanceof ConstantValue ||
          a instanceof Signature) {
        if (!an_existing.contains(getMapping().getAttributeSecondValue(a))) {
          ansce.addNumber(getMapping().getAttributeSecondValue(a));
          was_error = true;
        }
      } else if (a instanceof ExceptionTable) {
        final ExceptionTable et = (ExceptionTable) a;
        for (int i = 0; i < et.getExceptionIndexTable().length; i++) {
          if (!an_existing.
              contains(getMapping().getExceptionTable(et)[i])) {
            ansce.addNumber(getMapping().getExceptionTable(et)[i]);
            was_error = true;
          }
        }
      } else if (a instanceof PMGClass) {
        final PMGClass pmgc = (PMGClass) a;
        if (!an_existing.contains(getMapping().getPMGClass(pmgc))) {
          ansce.addNumber(getMapping().getPMGClass(pmgc));
          was_error = true;
        }
        if (!an_existing.contains(getMapping().getAttributeSecondValue(pmgc))) {
          ansce.addNumber(getMapping().getAttributeSecondValue(pmgc));
          was_error = true;
        }
      }
      if (was_error) a_report.addError(ansce);
    }
  }

}
