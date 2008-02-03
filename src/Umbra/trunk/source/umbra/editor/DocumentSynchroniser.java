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
import org.apache.bcel.classfile.Method;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

import umbra.UmbraPlugin;
import annot.textio.CodeFragment;

/**
 * This class handles the logic of the synchronisation of the cursor positions
 * between the source code and the byte code documents. It computes for a given
 * source code line a corresponding byte code line and for a given byte code
 * line the corresponding source code line range. It uses the class file line
 * number table to perform these operations.
 *
 * FIXME: more documentation is needed
 * FIXME: this does not take into account the modification of the byte code
 *        files
 * FIXME: the implementation is too horrible to be usable, it must be rewritten
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
   * The number of lines at the beginning of a method which are unrelated to the
   * synchronisation. We have to skip the method header when the document
   * structure is analysed.
   */
  private static final int SYNC_INCREMENT = 2;

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
   * @see #synchronizeSB(int, IEditorPart)
   * @param a_pos index of line in byte code editor. Lines in related source
   *   code editor corresponding to this line will be highlighted.
   */
  public final void synchronizeBS(final int a_pos) {
    try {
      final int line = my_bcode_doc.getLineOfOffset(a_pos);
      // syncBS computes the area to highlight
      final int[] syncLine = syncBS(my_bcode_doc.getJavaClass(), line);
      final int syncPos = my_java_doc.getLineOffset(syncLine[0]);
      final int syncLen = my_java_doc.getLineOffset(syncLine[1] + 1) - syncPos;
      final CompilationUnitEditor jeditor = my_bcode_doc.getRelatedEditor();
      jeditor.getEditorSite().getPage().activate(jeditor);
      if (syncLen < 0) MessageDialog.openError(new Shell(), "Bytecode",
                                               "Synchronisation failed");
      else jeditor.getSelectionProvider().
                   setSelection(new TextSelection(syncPos, syncLen));
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
  }

  /**
   * Computes the area in current java source code corresponding to given line
   * of byte code. The byte code should be refreshed before calling this metod,
   * to update JavaClass structures. Works correctly only inside a method.
   *
   * @param a_java_class  JavaClass with current byte code
   * @param a_line_no  index of line in byte code editor
   * @return array of 2 ({@link #NO_OF_POSITIONS}) ints representing index of
   *         first and last line of
   *         source code (corresponding to given byte code line),
   *         in related source code editor
   * @throws BadLocationException if line parameter is invalid. May occur also
   *         if byte code in JavaClass jc is out-of-date.
   */
  private int[] syncBS(final JavaClass a_java_class,
                       final int a_line_no) throws BadLocationException
  // Synchronisation: Btc --> Src
  {
    final String code = my_bcode_doc.get();
    /* XXX changed! uses bmllib to correct input selection in case of
     * selecting BML annotation.
     */
    final int a_line_no1 = CodeFragment.goDown(code, a_line_no);
    final int[] res = new int[NO_OF_POSITIONS];
    final int maxL = my_java_doc.getNumberOfLines() - 1;
    int l_od = 0;
    int l_do = maxL;
    int pos = 0;
    int posln = 0;
    int pop = 0;
    int lnr = 0;
    int lnrmax = 0;
    int l, j, pc;
    int endpos = 0;
    final Method[] methods = a_java_class.getMethods();
    Method m;
    for (int i = 0; i < methods.length; i++) {
      m = methods[i];
      pos += SYNC_INCREMENT; //skip method header?
      l = m.getLineNumberTable().getLineNumberTable().length;
      for (j = 0; j < l; j++) {
        pop = lnr;
        lnr = m.getLineNumberTable().getLineNumberTable()[j].
                                     getLineNumber() - 1;
        if (lnr > lnrmax)
          lnrmax = lnr;
        pc = m.getLineNumberTable().getLineNumberTable()[j].getStartPC();
        do {
          pos = my_bcode_doc.get().indexOf("" + pc + ":", pos + 1);
          if (pos == -1) {
            break;
          }
        } while (my_bcode_doc.getLineOfOffset(pos - 1) ==
                 my_bcode_doc.getLineOfOffset(pos));
        // "<pc>:" is located at the beginning of a line
        if (pos == -1) {
          if (l_od != 0)
            l_do = l_od;
          UmbraPlugin.messagelog("syncBS: ERROR - a position not found in " +
                                 "LineNumberTable!");
          break;
        }
        posln = my_bcode_doc.getLineOfOffset(pos);
        if (posln == a_line_no1) {
          l_od = lnr;
        }
        if (posln > a_line_no1) {
          l_od = pop;
          l_do = lnrmax - 1;
          if (endpos > 0)
            l_do = endpos;
          break;
        }
        endpos = 0;
      }
      if (j != l)
        break;
      endpos = lnrmax;
      if (l_od > 0) {
        l_do = endpos;
        break;
      }
    }
    if ((l_od == 0) && (l_do == maxL))
      l_od = maxL - 1;
    if (l_do == maxL)
      l_do--;
    if (l_od > l_do)  // fixed
      l_do = l_od;
    res[0] = l_od;
    res[1] = l_do;
    return res;
  }

  /**
   * Highlights the area in the byte code editor which corresponds to the
   * marked position in the source code editor. Works correctly only when the
   * position {@code a_pos} is inside a method. We assume that the current
   * Java document is edited in the given Java editor.
   *
   * @see #synchronizeBS(int)
   * @param a_pos index of line in source code editor. Lines in related byte
   *       code editor corresponding  to this line will be highlighted
   * @param an_editor the source code editor
   */
  public final void synchronizeSB(final int a_pos,
                                  final IEditorPart an_editor) {
    try {
      final int line = my_java_doc.getLineOfOffset(a_pos);
      final int[] syncLine = syncSB(my_bcode_doc.getJavaClass(), line);
      final int syncPos = my_bcode_doc.getLineOffset(syncLine[0]);
      final int syncLen = my_bcode_doc.getLineOffset(syncLine[1] + 1) - syncPos;
      an_editor.getEditorSite().getPage().activate(an_editor);
      if (syncLen < 0) MessageDialog.openError(new Shell(), "Bytecode",
                                               "Synchronisation failed");
      else ((AbstractDecoratedTextEditor)an_editor).getSelectionProvider().
                             setSelection(new TextSelection(syncPos, syncLen));
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
  }

  /**
   * Computes the area in the current byte code corresponding to the given line
   * of the source code. The byte code should be refreshed before calling this
   * method, to update {@link JavaClass} structures. Works correctly only inside
   * a method.
   *
   * @param a_java_class {@link JavaClass} with current byte code
   * @param a_line_no an index of line in <code>a_source_doc</code>
   * @return array of 2 ({@link #NO_OF_POSITIONS}) ints representing index of
   *         first and last line of byte code (corresponding to given source
   *         line), in the related byte code editor
   * @throws BadLocationException if line parameter is invalid. May occur also
   *         if byte code in {@link JavaClass} <code>a_java_class</code>
   *         is out-of-date.
   */
  private int[] syncSB(final JavaClass a_java_class,
                       final int a_line_no) throws BadLocationException {
    final String code = my_bcode_doc.get();
    final int[] result = new int [NO_OF_POSITIONS];
    int j, a_line_num_tablelen, pc, ln;
    int bcln = 0;
    int popln = 0;
    final int maxL = my_bcode_doc.getNumberOfLines() - 1;
    int l_od = 0;
    int l_do = maxL;
    String a_src_line = my_java_doc.get(my_java_doc.getLineOffset(a_line_no),
                                      my_java_doc.getLineLength(a_line_no)) +
                                      "$";
    while ((a_src_line.length() > 1) &&
           (Character.isWhitespace(a_src_line.charAt(0))))
      a_src_line = a_src_line.substring(1, a_src_line.length() - 1);
    String s;
    final Method[] methods = a_java_class.getMethods();
    Method m;
    for (int i = 0; i < methods.length; i++) {
      m = methods[i];
      a_line_num_tablelen = m.getLineNumberTable().getLineNumberTable().length;
      if (a_src_line.startsWith(m.toString())) {
        while (bcln < maxL) {
          bcln++;
          s = lineAt(bcln);
          if (s.startsWith("Code"))
            break;
        }
        l_od = bcln - 1;
        l_do = bcln - 1;
        break;
      }
      l_do = -1;
      for (j = 0; j < a_line_num_tablelen; j++) {
        pc = m.getLineNumberTable().getLineNumberTable()[j].getStartPC();
        ln = m.getLineNumberTable().getLineNumberTable()[j].getLineNumber() - 1;
        popln = bcln;
        while (bcln < maxL) {
          bcln++;
          s = lineAt(bcln);
          if (s.startsWith("" + pc + ":"))
            break;
        }
        if (ln == a_line_no) {
          l_od = bcln;
          continue;
        }
        if ((ln > a_line_no) && (l_od == 0)) {
          l_od = popln;
          l_do = bcln - 1;
          break;
        }
        if ((l_od != 0) && (ln != a_line_no)) {
          l_do = bcln - 1;
          break;
        }
        if (ln == maxL)
          break;
      }
      if ((l_od != 0) && (l_do == -1)) {
        while (bcln < maxL) {
          bcln++;
          s = lineAt(bcln);
          if (s.lastIndexOf(":") == -1)
            break;
        }
        l_do = bcln - 1;
        break;
      }
      if (j < a_line_num_tablelen)
        break;
      if ((l_od != 0) && (l_do == maxL)) {
        l_do = l_od;
        break;
      }
    }
    if ((l_od == 0) && (l_do == maxL))
      l_od = maxL;
    //XXX changed! uses bmllib to extend result fragment by BML annotations.
    result[0] = CodeFragment.goUp(code, l_od);
    result[1] = CodeFragment.goDown(code, l_do);
    return result;
  }

  /**
   * Gives specified line of the current byte code.
   *
   * @param a_line  index of line in byte code editor (starting from 0).
   * Must be non-negative and less than number of lines in byte code editor.
   * @return  n-th line in byte code editor
   * @throws BadLocationException  occurs when parameter n isn't a valid line
   *        number.
   */
  private String lineAt(final int a_line) throws BadLocationException {
    return my_bcode_doc.get(my_bcode_doc.getLineOffset(a_line),
               my_bcode_doc.getLineLength(a_line));
  }

}
