/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

import umbra.UmbraPlugin;

/**
 * This class is related to document structure of bytecode
 * file and supplies it with synchronization tools (in both directions).
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLDocument extends Document {

  /**
   * TODO.
   */
  private static final int NO_OF_POSITIONS = 2;

  /**
   * TODO: why we increase by 2?
   */
  private static final int SYNC_INCREMENT = 2;

  /**
   * TODO.
   */
  private CompilationUnitEditor my_related_editor;

  /**
   * TODO.
   */
  private JavaClass my_javaclass;

  /**
   * TODO.
   */
  private ClassGen my_classgen;

  /**
   * TODO.
   * @param an_editor TODO
   */
  public final void setRelatedEditor(final CompilationUnitEditor an_editor) {
    my_related_editor = an_editor;
  }

  /**
   * @return the Java source code editor corresponding to the current
   * bytecode file
   */
  public final CompilationUnitEditor getRelatedEditor() {
    return my_related_editor;
  }

  /**
   * TODO.
   *
   * @param a_javaclass TODO
   */
  public final void setJavaClass(final JavaClass a_javaclass) {
    my_javaclass = a_javaclass;
  }

  /**
   * TODO.
   *
   * @return TODO
   */
  public final JavaClass getJavaClass() {
    return my_javaclass;
  }

  /**
   * TODO.
   * @param a_class_gen TODO
   */
  public final void setClassGen(final ClassGen a_class_gen) {
    my_classgen = a_class_gen;
  }

  /**
   * TODO.
   * @return TODO
   */
  public final ClassGen getClassGen() {
    return my_classgen;
  }

  /* synchronization of cursor's positions */

  /**
   * Highlights the area computed in
   * {@link #syncBS(IDocument, JavaClass, int) syncBS} method in related source
   * code editor. Works correctly only inside a method.
   *
   * @param a_pos index of line in bytecode editor. Lines in related source code
   * editor correspondings to this line will be highlighted.
   * @see #synchronizeSB(int, IEditorPart)
   */
  public final void synchronizeBS(final int a_pos) {
    final IDocument sDoc = my_related_editor.getDocumentProvider().
                                getDocument(my_related_editor.getEditorInput());
    try {
      final int line = getLineOfOffset(a_pos);
      final int[] syncLine = syncBS(sDoc, my_javaclass, line);
      final int syncPos = sDoc.getLineOffset(syncLine[0]);
      final int syncLen = sDoc.getLineOffset(syncLine[1] + 1) - syncPos;
      UmbraPlugin.messagelog("sync(" + syncLine[0] + ", " + syncLine[1] + ")");
      my_related_editor.getEditorSite().getPage().activate(my_related_editor);
      if (syncLen < 0) MessageDialog.openError(new Shell(), "BoogiePL",
                                               "Synchronisation failed");
      else my_related_editor.getSelectionProvider().
                         setSelection(new TextSelection(syncPos, syncLen));
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
  }

  /**
   * Computes the area in current java source code corresponding to given
   * line of bytecode. The bytecode should be refreshed before calling this
   * metod, to update JavaClass structures. Works correctly only inside a
   * method.
   *
   * @param a_source_doc  IDocument with source (java) code
   * @param a_java_class  JavaClass with current bytecode
   * @param a_line_index  index of line in bytecode editor
   * @return    array of two ints representing index of first and last line of
   *         source code (corresponding to given bytecode line),
   *         in related source code editor
   * @throws BadLocationException if line parameter is invalid. May occur also
   *         if bytecode in JavaClass jc is out-of-date.
   */
  private int[] syncBS(final IDocument a_source_doc,
                       final JavaClass a_java_class,
                       final int a_line_index) throws BadLocationException
  // Synchronizacja: Btc --> Src
  {
    final int[] w = new int[NO_OF_POSITIONS];
    final int maxL = a_source_doc.getNumberOfLines() - 1;
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
      pos += SYNC_INCREMENT;
      l = m.getLineNumberTable().getLineNumberTable().length;
      for (j = 0; j < l; j++) {
        pop = lnr;
        lnr = m.getLineNumberTable().getLineNumberTable()[j].
                                     getLineNumber() - 1;
        if (lnr > lnrmax)
          lnrmax = lnr;
        pc = m.getLineNumberTable().getLineNumberTable()[j].getStartPC();
        do {
          pos = get().indexOf("" + pc + ":", pos + 1);
          if (pos == -1) {
            break;
          }
        } while (getLineOfOffset(pos - 1) == getLineOfOffset(pos));
        // "<pc>:" musi by� znalezione na pocz�tku linii.
        if (pos == -1) {
          if (l_od != 0)
            l_do = l_od;
          UmbraPlugin.messagelog("syncBS: ERROR - a position not found in " +
                                 "LineNumberTable!");
          break;
        }
        posln = getLineOfOffset(pos);
        if (posln == a_line_index) {
          l_od = lnr;
        }
        if (posln > a_line_index) {
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
    w[0] = l_od;
    w[1] = l_do;
    return w;
  }

  /**
   * Highlights the area computed in {@link #syncSB(IDocument, JavaClass, int)
   * syncSB} method in related bytecode editor. Works correctly only inside a
   * method.
   *
   * @param a_pos index of line in source code editor. Lines in related bytecode
   *       editor correspondings to this line will be highlighted.
   * @param an_editor the source code editor
   * @see #synchronizeBS(int)
   */
  public final void synchronizeSB(final int a_pos,
                                  final IEditorPart an_editor) {
    final IDocument sDoc = my_related_editor.getDocumentProvider().
                                getDocument(my_related_editor.getEditorInput());
    try {
      final int line = sDoc.getLineOfOffset(a_pos);
      final int[] syncLine = syncSB(sDoc, my_javaclass, line);
      final int syncPos = getLineOffset(syncLine[0]);
      final int syncLen = getLineOffset(syncLine[1] + 1) - syncPos;
      an_editor.getEditorSite().getPage().activate(an_editor);
      if (syncLen < 0) MessageDialog.openError(new Shell(), "BoogiePL",
                                               "Synchronisation failed");
      else ((AbstractDecoratedTextEditor)an_editor).getSelectionProvider().
                              setSelection(new TextSelection(syncPos, syncLen));
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
  }

  /**
   * Computes the area in current bytecode corresponding to given line of
   * source code. The bytecode should be refreshed before calling this metod,
   * to update {@ref JavaClass} structures. Works correctly only inside
   * a method.
   *
   * @param a_source_doc {@ref IDocument} with the Java source code
   * @param a_javaclass {@ref JavaClass} with current bytecode
   * @param a_lineno index of line in <code>a_source_doc</code>
   * @return array of 2 ({@ref #NO_OF_POSITIONS}) ints representing index of
   *         first and last line of bytecode (corresponding to given source
   *         line), in related bytecode editor
   * @throws BadLocationException if line parameter is invalid. May occur also
   *         if bytecode in {@ref JavaClass} <code>a_javaclass</code> is
   *         out-of-date.
   */
  private int[] syncSB(final IDocument a_source_doc,
                       final JavaClass a_javaclass,
                       final int a_lineno) throws BadLocationException
  // Synchronizacja Src --> Btc
  {
    final int[] result = new int [NO_OF_POSITIONS];
    int j, l, pc, ln;
    int bcln = 0;
    int popln = 0;
    final int maxL = getNumberOfLines() - 1;
    int l_od = 0;
    int l_do = maxL;
    String src_line = a_source_doc.get(a_source_doc.getLineOffset(a_lineno),
                              a_source_doc.getLineLength(a_lineno)) + "$";
    while ((src_line.length() > 1) &&
           (Character.isWhitespace(src_line.charAt(0))))
      src_line = src_line.substring(1, src_line.length() - 1);
    String s;
    final Method[] methods = a_javaclass.getMethods();
    Method m;
    for (int i = 0; i < methods.length; i++) {
      m = methods[i];
      l = m.getLineNumberTable().getLineNumberTable().length;
      if (src_line.startsWith(m.toString())) {
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
      for (j = 0; j < l; j++) {
        pc = m.getLineNumberTable().getLineNumberTable()[j].getStartPC();
        ln = m.getLineNumberTable().getLineNumberTable()[j].getLineNumber() - 1;
        popln = bcln;
        while (bcln < maxL) {
          bcln++;
          s = lineAt(bcln);
          if (s.startsWith("" + pc + ":"))
            break;
        }
        if (ln == a_lineno) {
          l_od = bcln;
          continue;
        }
        if ((ln > a_lineno) && (l_od == 0)) {
          l_od = popln;
          l_do = bcln - 1;
          break;
        }
        if ((l_od != 0) && (ln != a_lineno)) {
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
      if (j < l)
        break;
      if ((l_od != 0) && (l_do == maxL)) {
        l_do = l_od;
        break;
      }
    }
    if ((l_od == 0) && (l_do == maxL))
      l_od = maxL;
    result[0] = l_od;
    result[1] = l_do;
    return result;
  }

  /**
   * Gives specified line of current bytecode.
   *
   * @param a_lineno  index of line in bytecode editor (starting from 0).
   * Must be non-negative and less than number of lines in bytecode editor.
   * @return  n-th line in bytecode editor
   * @throws BadLocationException  occurs when parameter n isn't a valid line
   *                               number.
   */
  private String lineAt(final int a_lineno) throws BadLocationException
  // n-ta linia dokumentu d
  {
    return get(getLineOffset(a_lineno), getLineLength(a_lineno));
  }

}
