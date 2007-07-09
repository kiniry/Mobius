/*
 * Created on 2005-06-18
 *
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
  private CompilationUnitEditor fRelatedEditor;
  /**
   * TODO.
   */
  private JavaClass fJavaClass;
  /**
   * TODO.
   */
  private ClassGen classGen;

  /**
   * TODO.
   * @param an_editor TODO
   */
  public final void setRelatedEditor(final CompilationUnitEditor an_editor) {
    fRelatedEditor = an_editor;
  }

  /**
   * @return the Java source code editor corresponding to the current
   * bytecode file
   */
  public final CompilationUnitEditor getRelatedEditor() {
    return fRelatedEditor;
  }

  /**
   * TODO.
   *
   * @param a_javaclass TODO
   */
  public final void setJavaClass(final JavaClass a_javaclass) {
    fJavaClass = a_javaclass;
  }

  /**
   * TODO.
   *
   * @return TODO
   */
  public final JavaClass getJavaClass() {
    return fJavaClass;
  }

  /**
   * TODO.
   * @param a_class_gen TODO
   */
  public final void setClassGen(final ClassGen a_class_gen) {
    classGen = a_class_gen;
  }

  /**
   * TODO.
   * @return TODO
   */
  public final ClassGen getClassGen() {
    return classGen;
  }

  /* synchronization of cursor's positions */

  /**
   * Highlights the area computed in
   * {@link #syncBS(IDocument, JavaClass, int) syncBS} method in related source
   * code editor. Works correctly only inside a method.
   *
   * @see #synchronizeSB(int, IEditorPart)
   * @param pos  index of line in bytecode editor. Lines in related source code
   * editor correspondings to this line will be highlighted.
   */
  public final void synchronizeBS(final int pos) {
    final IDocument sDoc = fRelatedEditor.getDocumentProvider().
                                getDocument(fRelatedEditor.getEditorInput());
    try {
      final int line = getLineOfOffset(pos);
      final int[] syncLine = syncBS(sDoc, fJavaClass, line);
      final int syncPos = sDoc.getLineOffset(syncLine[0]);
      final int syncLen = sDoc.getLineOffset(syncLine[1] + 1) - syncPos;
      UmbraPlugin.messagelog("sync(" + syncLine[0] + ", " + syncLine[1] + ")");
      fRelatedEditor.getEditorSite().getPage().activate(fRelatedEditor);
      if (syncLen < 0) MessageDialog.openError(new Shell(), "BoogiePL",
                                               "Synchronisation failed");
      else fRelatedEditor.getSelectionProvider().
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
          UmbraPlugin.messagelog("syncBS: b��d -- nie znaleziono kolejnej " +
                                 "pozycji z LineNumberTable!");
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
   * @see #synchronizeBS(int)
   * @param pos  index of line in source code editor. Lines in related bytecode
   *       editor correspondings to this line will be highlighted.
   * @param editor the source code editor
   */
  public final void synchronizeSB(final int pos, final IEditorPart editor) {
    final IDocument sDoc = fRelatedEditor.getDocumentProvider().
                                  getDocument(fRelatedEditor.getEditorInput());
    try {
      final int line = sDoc.getLineOfOffset(pos);
      final int[] syncLine = syncSB(sDoc, fJavaClass, line);
      final int syncPos = getLineOffset(syncLine[0]);
      final int syncLen = getLineOffset(syncLine[1] + 1) - syncPos;
      editor.getEditorSite().getPage().activate(editor);
      if (syncLen < 0) MessageDialog.openError(new Shell(), "BoogiePL",
                                               "Synchronisation failed");
      else ((AbstractDecoratedTextEditor)editor).getSelectionProvider().
                              setSelection(new TextSelection(syncPos, syncLen));
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
  }

  /**
   * Computes the area in current bytecode corresponding to given line of
   * source code. The bytecode should be refreshed before calling this metod,
   * to update JavaClass structures. Works correctly only inside a method.
   *
   * @param Sdoc  IDocument with source (java) code
   * @param jc  JavaClass with current bytecode
   * @param line  index of line in Sdoc
   * @return    array of two ints representing index of first and last line of
   *         bytecode (corresponding to given source line),
   *         in related bytecode editor
   * @throws BadLocationException if line parameter is invalid. May occur also
   *         if bytecode in JavaClass jc is out-of-date.
   */
  private int[] syncSB(final IDocument Sdoc,
                       final JavaClass jc,
                       final int line) throws BadLocationException
  // Synchronizacja Src --> Btc
  {
    final int[] result = new int [NO_OF_POSITIONS];
    int j, l, pc, ln;
    int bcln = 0;
    int popln = 0;
    final int maxL = getNumberOfLines() - 1;
    int l_od = 0;
    int l_do = maxL;
    String SrcLine = Sdoc.get(Sdoc.getLineOffset(line),
                              Sdoc.getLineLength(line)) + "$";
    while ((SrcLine.length() > 1) &&
           (Character.isWhitespace(SrcLine.charAt(0))))
      SrcLine = SrcLine.substring(1, SrcLine.length() - 1);
    String s;
    final Method[] methods = jc.getMethods();
    Method m;
    for (int i = 0; i < methods.length; i++) {
      m = methods[i];
      l = m.getLineNumberTable().getLineNumberTable().length;
      if (SrcLine.startsWith(m.toString())) {
        while (bcln < maxL) {
          bcln++;
          s = LineAt(bcln);
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
          s = LineAt(bcln);
          if (s.startsWith("" + pc + ":"))
            break;
        }
        if (ln == line) {
          l_od = bcln;
          continue;
        }
        if ((ln > line) && (l_od == 0)) {
          l_od = popln;
          l_do = bcln - 1;
          break;
        }
        if ((l_od != 0) && (ln != line)) {
          l_do = bcln - 1;
          break;
        }
        if (ln == maxL)
          break;
      }
      if ((l_od != 0) && (l_do == -1)) {
        while (bcln < maxL) {
          bcln++;
          s = LineAt(bcln);
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
   * @param n  index of line in bytecode editor (starting from 0).
   * Must be non-negative and less than number of lines in bytecode editor.
   * @return  n-th line in bytecode editor
   * @throws BadLocationException  occurs when parameter n isn't a valid line
   *                               number.
   */
  private String LineAt(final int n) throws BadLocationException
  // n-ta linia dokumentu d
  {
    return get(getLineOffset(n), getLineLength(n));
  }

}
