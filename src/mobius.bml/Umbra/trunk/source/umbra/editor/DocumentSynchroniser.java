/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.LineNumber;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

import umbra.instructions.BytecodeController;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraException;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraSynchronisationException;

/**
 * This class handles the logic of the synchronisation of the cursor positions
 * between the source code and the byte code documents. It computes for a given
 * source code line a corresponding byte code line and for a given byte code
 * line the corresponding source code line range. It uses the class file line
 * number table to perform these operations.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class DocumentSynchroniser {

  /**
   * This is the size of the array which contains the range of positions of the
   * target document (e.g. source code) that corresponds to the initial position
   * in the initial document (e.g. byte code).
   */
  private static final int NO_OF_POSITIONS = 2;

  /**
   * The byte code document which takes part in the synchronisation process.
   */
  private BytecodeDocument my_bcode_doc;

  /**
   * The Java source code document which takes part in the synchronisation
   * process.
   */
  private IDocument my_java_doc;

  /**
   * The constructor initialises the relation between the byte code document
   * and the source code document to make the synchronisation with.
   *
   * @param a_bdoc the byte code document
   * @param a_jdoc the Java source code document
   */
  public DocumentSynchroniser(final BytecodeDocument a_bdoc,
                                final IDocument a_jdoc) {
    my_bcode_doc = a_bdoc;
    my_java_doc = a_jdoc;
  }

  /**
   * Highlights the area in the source code editor which corresponds to
   * the marked area in the byte code editor. Works correctly only inside a
   * method body.
   *
   * @see DocumentSynchroniser#synchronizeSB(int, CompilationUnitEditor)
   * @param a_pos index of line in byte code editor. Lines in related source
   *   code editor corresponding to this line will be highlighted.
   * @throws UmbraLocationException in case a position is reached in the
   *   source code or byte code editor which does not exists there
   * @throws UmbraSynchronisationException in case there is no instruction
   *   line which can be reasonably associated with the given position
   */
  public final void synchronizeBS(final int a_pos)
    throws UmbraLocationException, UmbraSynchronisationException {
    int line;
    try {
      line = my_bcode_doc.getLineOfOffset(a_pos);
    } catch (BadLocationException e1) {
      throw new UmbraLocationException(true, a_pos, false);
    }
    // syncBS computes the area to highlight
    final int syncLine;
    try {
      syncLine = syncBS(my_bcode_doc.getJavaClass(), line);
    } catch (UmbraException e1) {
      throw new UmbraSynchronisationException();
    }
    final int syncPos;
    try {
      syncPos = my_java_doc.getLineOffset(syncLine);
    } catch (BadLocationException e) {
      throw new UmbraLocationException(false, syncLine, true);
    }
    int synclen;
    try {
      synclen = my_java_doc.getLineOffset(syncLine + 1) - syncPos;
    } catch (BadLocationException e) {
      throw new UmbraLocationException(false, syncLine + 1, true);
    }
    final CompilationUnitEditor jeditor =
      my_bcode_doc.getEditor().getRelatedEditor();
    jeditor.getEditorSite().getPage().activate(jeditor);
    if (synclen < 0) {
      MessageDialog.openError(my_bcode_doc.getEditor().getSite().getShell(),
        GUIMessages.BYTECODE_MESSAGE_TITLE,
        GUIMessages.WRONG_SYNCHRONISATION_MSG);
    } else jeditor.getSelectionProvider().
                 setSelection(new TextSelection(syncPos, synclen));
  }

  /**
   * Computes the area in current Java source code corresponding to given line
   * of the byte code document. The byte code should be refreshed before calling
   * this method to update JavaClass structures. Works correctly only inside a
   * method.
   *
   * Algorithm:
   * <ul>
   *   <li>We obtain the number of the first instruction line not above the
   *       given position (we synchronise the BML annotations and comments
   *       so that the instruction below them is considered to be a pointer
   *       to the source code).</li>
   *   <li>We obtain the number of the method which contains the line (to
   *       be able to use the LineNumberTable).</li>
   *   <li>We retrieve the label of the instruction line we found (as the
   *       positions in the LineNumberTable are indexed with the labels).</li>
   *   <li>We look for the highest byte code label number in the LineNumberTable
   *       which is lower than the one we have already found (the entries in
   *       show where the source code line number changes, if there is no
   *       current label there then the current source code line begins at line
   *       with some lower label).</li>
   *   <li>We return the source code line from this entry in the
   *       LineNumberTable</li>
   * </ul>
   *
   * @param classGen {@link org.apache.bcel.classfile.JavaClass} with
   *   current byte code BCEL representation
   * @param a_line_no index of line in byte code editor
   * @return the line of the source code corresponding to given byte code
   *   line)
   * @throws UmbraException in case there is no instruction line that can be
   *   reasonably associated with the given line number
   * @throws UmbraSynchronisationException in case there is no instruction
   *   line that can be reasonably associated with the given line number
   */
  private int syncBS(final ClassGen classGen,
                     final int a_line_no)
    throws UmbraException, UmbraSynchronisationException {
    final BytecodeController model = my_bcode_doc.getModel();
    final int lineno = model.getInstructionLineBelow(a_line_no);
    final int mno = model.getMethodForLine(lineno);
    final int label = model.getLabelForLine(lineno);
    final Method m = classGen.getMethods()[mno];
    if (m.getLineNumberTable() == null)
      throw new UmbraSynchronisationException();
    final LineNumber[] lnt = m.getLineNumberTable().getLineNumberTable();
    int minpc = 0;
    int imin = 0;
    for (int i = 0; i < lnt.length; i++) {
      final int cpc = lnt[i].getStartPC();
      if (minpc <  cpc && cpc <= label) {
        minpc = cpc;
        imin = i;
      }
    }
    return lnt[imin].getLineNumber() - 1; //lines in lnt start with 1
  }

  /**
   * Highlights the area in the byte code editor which corresponds to the
   * marked position in the source code editor. Works correctly only when the
   * position {@code a_pos} is inside a method. We assume that the current
   * Java document is edited in the given Java editor.
   *
   * @see #synchronizeBS(int)
   * @param a_pos a position in the source code editor. Lines in related byte
   *   code editor containing the line with this position will
   *   be highlighted
   * @param an_editor the source code editor
   * @throws UmbraLocationException in case a reference in a document is made
   *   to a position outside the document
   * @throws UmbraSynchronisationException  in case the synchronisation is
   *   scheduled for a position outside the method body
   * @throws JavaModelException a Java element cannot be accessed
   */
  public final void synchronizeSB(final int a_pos,
                                  final CompilationUnitEditor an_editor)
    throws UmbraLocationException, UmbraSynchronisationException,
           JavaModelException {
    final int[] syncLine;
    syncLine = syncSB(my_bcode_doc.getJavaClass(), an_editor, a_pos);
    final int syncPos;
    try {
      syncPos = my_bcode_doc.getLineOffset(syncLine[0]);
    } catch (BadLocationException e) {
      throw new UmbraLocationException(false, syncLine[0], true);
    }
    final int syncLen;
    try {
      syncLen = my_bcode_doc.getLineOffset(syncLine[1] + 1) - syncPos;
    } catch (BadLocationException e) {
      throw new UmbraLocationException(false, syncLine[1], true);
    }
    if (syncLen < 0) {
      MessageDialog.openInformation(an_editor.getSite().getShell(),
        GUIMessages.BYTECODE_MESSAGE_TITLE,
        GUIMessages.WRONG_SYNCHRONISATION_MSG);
      an_editor.getEditorSite().getPage().activate(an_editor);
    } else {
      final BytecodeEditor be = my_bcode_doc.getEditor();
      an_editor.getEditorSite().getPage().activate(be);
      ((AbstractDecoratedTextEditor)be).selectAndReveal(syncPos, syncLen);
    }
  }

  /**
   * Computes the area in the current byte code corresponding to the given line
   * of the source code. The byte code should be refreshed before calling this
   * method, to update {@link JavaClass} structures. Works correctly only inside
   * a method.
   *
   * FIXME: we rely now on the fact that the sequence of methods in the
   *   source code is the same as in the byte code (which need not be true
   *   in general), a better way to synchronise would be to resolve the name
   *   and the signature of the method
   *   https://mobius.ucd.ie/ticket/595
   *
   * @param classGen {@link JavaClass} with current byte code
   * @param an_editor Java source code editor
   * @param a_pos a position in the source code to synchronise with
   * @return array of 2 ({@link #NO_OF_POSITIONS}) ints representing index of
   *         first and last line of byte code (corresponding to given source
   *         line), in the related byte code editor
   * @throws UmbraSynchronisationException in case the sychronisation is
   *   scheduled for a position outside the method body
   * @throws JavaModelException a Java element cannot be accessed
   * @throws UmbraLocationException if the position parameter is outside the
   *   Java source code. May occur also if byte code in {@link JavaClass}
   *   <code>a_java_class</code> is out-of-date.
   */
  private int[] syncSB(final ClassGen classGen,
                       final CompilationUnitEditor an_editor,
                       final int a_pos)
    throws UmbraSynchronisationException,
           JavaModelException, UmbraLocationException {
    final Method[] methods = classGen.getMethods();

    final int mno = getSrcMethodNumber(a_pos, an_editor,
                                    classGen.getClassName()) + 1;
                                    // +1 for <init>
    final Method m = methods[mno];
    int line;
    try {
      line = my_java_doc.getLineOfOffset(a_pos);
    } catch (BadLocationException e) {
      throw new UmbraLocationException(false, a_pos, false);
    }
    final int[] result = handleInsideMethod(line, mno,
                                  m.getLineNumberTable().getLineNumberTable());
    return result;
  }

  /**
   * The method returns the method number of a method in the source code
   * document. It retrieves the number of the method the body of which contains
   * the given position.
   *
   * @param a_pos the position to find the method for
   * @param an_editor the editor in which the source code is edited
   * @param a_class_name the name of the class in the edited source code in
   *   which the method is located
   * @return the number of the method in the source code
   * @throws JavaModelException in case the access to the parsed source code
   *   cannot be made
   * @throws UmbraSynchronisationException there is no method for the given
   *   position in the given class
   */
  private int getSrcMethodNumber(final int a_pos,
                                 final CompilationUnitEditor an_editor,
                                 final String a_class_name)
    throws JavaModelException, UmbraSynchronisationException {
    final ICompilationUnit cu =
      JavaPlugin.getDefault().getWorkingCopyManager().
                              getWorkingCopy(an_editor.getEditorInput());
    final IType[] types = cu.getTypes();
    for (int i = 0; i < types.length; i++) {
      if (!types[i].getFullyQualifiedName().equals(a_class_name))
        continue;
      final IMethod[] methods = types[i].getMethods();
      for (int j = 0; j < methods.length; j++) {
        final IMethod meth = methods[j];
        final int start = meth.getSourceRange().getOffset();
        final int end = start + meth.getSourceRange().getLength();
        if (start <= a_pos && a_pos < end) {
          return j;
        }
      }
    }
    throw new UmbraSynchronisationException();
  }

  /**
   * The method finds the region in the byte code document which corresponds
   * to the given line which is located in the method of the given number.
   * We look for the given source code line number in the line number table.
   * In case the line is found, we look for the position in the line number
   * table which contains the lowest program counter greater than the
   * program counter for the given source code line number. We obtain in this
   * way a range of the byte code lines between the first program counter
   * value and the second one (excluding that). This range is returned.
   *
   * FIXME: note that this algorithm gives only one range whereas a particular
   *   line of the source code may be compiled into several disjoint ranges
   *   of the byte code instructions
   *   https://mobius.ucd.ie/ticket/595
   * FIXME: we assume that the source code has not changed between the
   *   synchronisation and the generation of the line number table
   *   https://mobius.ucd.ie/ticket/595
   *
   * @param a_line a line in the source code containing the position to
   *   synchronise with, lines start with 0
   * @param a_mno a method number located within the method
   * @param the_linenums the line number table
   * @return a array of 2 integers, the first one is the first line of the
   *   region, the second one is the last line of the region
   */
  private int[] handleInsideMethod(final int a_line,
                                   final int a_mno,
                                   final LineNumber[] the_linenums) {
    final int linetofind = a_line + 1; //lines in lnt start with 1
    int bstart = -1;
    int bend = -1;
    final BytecodeController model = my_bcode_doc.getModel();
    for (int j = 0; j < the_linenums.length; j++) {
      final int pc = the_linenums[j].getStartPC();
      final int srcln = the_linenums[j].getLineNumber();
      final int lineforpc = model.getLineForPCInMethod(pc, a_mno);
      if (srcln == linetofind) {
        final int nextpc = findNextLine(the_linenums, pc);
        bstart = lineforpc;
        if (nextpc > 0) {
          bend = model.getLineForPCInMethod(nextpc, a_mno) - 1;
        } else { // find the biggest pc in the method
          bend = model.getLastLineInMethod(a_mno);
        }
        break;
      }
    }
    final int[] result = new int[NO_OF_POSITIONS];
    result[0] = bstart;
    result[1] = bend;
    return result;
  }

  /**
   * The method returns the lowest program counter number greater than the
   * given one (i.e. the next pc number). We do the linear search for such a
   * counter.
   *
   * @param the_linenums the line number table to find the next pc number in
   * @param a_pc the program counter for which we seek the next pc number
   * @return the next pc number or -1 in case there is no bigger pc in the
   *   given line number table
   */
  private int findNextLine(final LineNumber[] the_linenums, final int a_pc) {
    int nextpc = -1;
    for (int i = 0; i < the_linenums.length; i++) {
      final int cpc = the_linenums[i].getStartPC();
      if (a_pc < cpc && ((cpc < nextpc) || nextpc == -1)) {
        nextpc = cpc;
      }
    }
    return nextpc;
  }

}
