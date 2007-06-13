/*
 * Created on 2005-06-18
 *
 */
package umbra.editor;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

/**
 * This class is an abstract model of a bytecode document.
 * It mainly handles the synchronization between a bytecode file and a
 * Java source code file (in both directions).
 *
 * FIXME more detailed description
 *
 * @author Tomasz Batkiewicz, Wojciech Wąs
 */
public class BytecodeDocument extends Document {

  /**
   * The Java source code editor for the source code file associated with
   * the current bytecode document.
   */
  private AbstractDecoratedTextEditor fRelatedEditor;

  /**
   * The representation of the Java class the content of which
   * we edint in the current document. The corresponding
   * class generator object is in the {@link #classGen}
   * field.
   */
  private JavaClass fJavaClass;
  //@ invariant bytecodeEditor.javaClass == fJavaClass;

  /**
   * The object to build Java classes. It is associated
   * with the {@link #fJavaClass} field.
   */
  private ClassGen classGen;
  //@ invariant bytecodeEditor.javaClass == fJavaClass;

  /**
   * The bytecode editor that manipulates the current document.
   */
  private BytecodeEditor bytecodeEditor;

  /**
   * The Java source code editor of the source code file associated
   * with the current bytecode document.
   *
   * @param editor updates the Java source code editor associated with the
   * current bytecode document.
   */
  public void setRelatedEditor(AbstractDecoratedTextEditor editor) {
    fRelatedEditor = editor;
  }

  /**
   * @return the Java source code editor associated with the
   * current bytecode document.
   */
  public AbstractDecoratedTextEditor getRelatedEditor() {
    return fRelatedEditor;
  }

  /**
   * The current representation of the Java class associated with
   * the document.
   */
  public JavaClass getJavaClass() {
    return fJavaClass;
  }

  /**
   * @return the current generator of the Java class file
   */
  public ClassGen getClassGen() {
    return classGen;
  }

  /* synchronization of cursor's positions */

  /**
   * Highlights the area computed in {@link #syncBS(IDocument, JavaClass, int) syncBS}
   * method in related source code editor. Works correctly only inside a method.
   *
   * @see #synchronizeSB(int, IEditorPart)
   * @param pos  index of line in bytecode editor. Lines in related source code
   * editor correspondings to this line will be highlighted.
   */
  public void synchronizeBS(int pos) {
    IDocument sDoc = fRelatedEditor.getDocumentProvider().getDocument(fRelatedEditor.getEditorInput());
    try {
      int line = getLineOfOffset(pos);
      int syncLine[] = syncBS(sDoc, fJavaClass, line);
      int syncPos = sDoc.getLineOffset(syncLine[0]);
      int syncLen = sDoc.getLineOffset(syncLine[1] + 1) - syncPos;
      System.out.println("sync("+syncLine[0]+", "+syncLine[1]+")");
      fRelatedEditor.getEditorSite().getPage().activate(fRelatedEditor);
      if (syncLen < 0) MessageDialog.openError(new Shell(), "Bytecode", "Synchronisation failed");
      else fRelatedEditor.getSelectionProvider().setSelection(new TextSelection(syncPos, syncLen));
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
  }

  /**
   * Computes the area in current java source code corresponding to given line of
   * bytecode. The bytecode should be refreshed before calling this metod,
   * to update JavaClass structures. Works correctly only inside a method.
   *
   * @param Sdoc  IDocument with source (java) code
   * @param jc  JavaClass with current bytecode
   * @param line  index of line in bytecode editor
   * @return    array of two ints representing index of first and last line of
   *         source code (corresponding to given bytecode line),
   *         in related source code editor
   * @throws BadLocationException if line parameter is invalid. May occur also
   *         if bytecode in JavaClass jc is out-of-date.
   */
  private int[] syncBS(IDocument Sdoc, JavaClass jc, int line) throws BadLocationException
  // Synchronizacja: Btc --> Src
  {
    int w[] = new int[2];
    int maxL = Sdoc.getNumberOfLines() - 1;
    int l_od = 0;
    int l_do = maxL;
    int pos = 0;
    int posln = 0;
    int pop = 0;
    int lnr = 0;
    int lnrmax = 0;
    int l, j, pc;
    int endpos = 0;
    Method[] methods = jc.getMethods();
    Method m;
    for (int i = 0; i < methods.length; i++) {
      m = methods[i];
      pos += 2;
      l = m.getLineNumberTable().getLineNumberTable().length;
      for (j = 0; j < l; j++) {
        pop = lnr;
        lnr = m.getLineNumberTable().getLineNumberTable()[j].getLineNumber() - 1;
        if (lnr > lnrmax)
          lnrmax = lnr;
        pc = m.getLineNumberTable().getLineNumberTable()[j].getStartPC();
        do {
          pos = get().indexOf("" + pc + ":", pos+1);
          if (pos == -1) {
            break;
          }
        } while (getLineOfOffset(pos-1) == getLineOfOffset(pos));
        // "<pc>:" musi by� znalezione na pocz�tku linii.
        if (pos == -1) {
          if (l_od != 0)
            l_do = l_od;
          System.out.println("syncBS: b��d -- nie znaleziono kolejnej pozycji z LineNumberTable!");
          break;
        }
        posln = getLineOfOffset(pos);
        if (posln == line) {
          l_od = lnr;
        }
        if (posln > line) {
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
   * Highlights the area computed in {@link #syncSB(IDocument, JavaClass, int) syncSB}
   * method in related bytecode editor. Works correctly only inside a method.
   *
   * @see #synchronizeBS(int)
   * @param pos  index of line in source code editor. Lines in related bytecode
   *       editor correspondings to this line will be highlighted.
   * @param editor the source code editor
   */
  public void synchronizeSB(int pos, IEditorPart editor) {
    IDocument sDoc = fRelatedEditor.getDocumentProvider().getDocument(fRelatedEditor.getEditorInput());
    try {
      int line = sDoc.getLineOfOffset(pos);
      int syncLine[] = syncSB(sDoc, fJavaClass, line);
      int syncPos = getLineOffset(syncLine[0]);
      int syncLen = getLineOffset(syncLine[1] + 1) - syncPos;
      editor.getEditorSite().getPage().activate(editor);
      if (syncLen < 0) MessageDialog.openError(new Shell(), "Bytecode", "Synchronisation failed");
      else ((AbstractDecoratedTextEditor)editor).getSelectionProvider().setSelection(new TextSelection(syncPos, syncLen));
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
  }

  /**
   * Computes the area in current bytecode corresponding to given line of source code.
   * The bytecode should be refreshed before calling this metod, to update JavaClass
   * structures. Works correctly only inside a method.
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
  private int[] syncSB(IDocument Sdoc, JavaClass jc, int line) throws BadLocationException
  // Synchronizacja Src --> Btc
  {
    int[] result = new int [2];
    int j, l, pc, ln;
    int bcln = 0;
    int popln = 0;
    int maxL = getNumberOfLines() - 1;
    int l_od = 0;
    int l_do = maxL;
    String SrcLine = Sdoc.get(Sdoc.getLineOffset(line), Sdoc.getLineLength(line)) + "$";
    while ((SrcLine.length() > 1) && (Character.isWhitespace(SrcLine.charAt(0))))
      SrcLine = SrcLine.substring(1, SrcLine.length() - 1);
    String s;
    Method methods[] = jc.getMethods();
    Method m;
    for (int i=0; i<methods.length; i++) {
      m = methods[i];
      l = m.getLineNumberTable().getLineNumberTable().length;
      if (SrcLine.startsWith(m.toString()) ) {
        while (bcln<maxL) {
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
      for (j=0; j<l; j++) {
        pc = m.getLineNumberTable().getLineNumberTable()[j].getStartPC();
        ln = m.getLineNumberTable().getLineNumberTable()[j].getLineNumber() - 1;
        popln = bcln;
        while (bcln<maxL) {
          bcln++;
          s = LineAt(bcln);
          if (s.startsWith("" + pc + ":"))
            break;
        }
        if (ln == line) {
          l_od = bcln;
          continue;
        };
        if ((ln > line) && (l_od == 0)) {
          l_od = popln;
          l_do = bcln - 1;
          break;
        };
        if ((l_od != 0) && (ln != line)) {
          l_do = bcln - 1;
          break;
        }
        if (ln == maxL)
          break;
      }
      if ((l_od != 0) && (l_do == -1)) {
        while (bcln<maxL) {
          bcln++;
          s = LineAt(bcln);
          if (s.lastIndexOf(":") == -1)
            break;
        }
        l_do = bcln - 1;
        break;
      };
      if (j<l)
        break;
      if ((l_od != 0) && (l_do == maxL)) {
        l_do = l_od;
        break;
      };
    }
    if ((l_od == 0) && (l_do == maxL))
      l_od = maxL;
    result[0] = l_od;
    result[1] = l_do;
    return result;
  }

  /**
   * Gives specified line of the current bytecode.
   *
   * @param n  index of line in bytecode editor (starting from 0).
   * Must be non-negative and less than number of lines in bytecode editor.
   * @return  n-th line in bytecode editor
   * @throws BadLocationException  occurs when parameter n isn't a valid line number.
   */
  private String LineAt(int n) throws BadLocationException
  {
    return get(getLineOffset(n), getLineLength(n));
  }

  /**
   * This method updates the bytecode editor associated with the
   * current document. Additionally, it updates the fields that
   * represent the bytecode of the document.
   *
   * @param editor the bytecode editor
   */
  public void setEditor(BytecodeEditor editor) {
    bytecodeEditor = editor;
    editor.setDocument(this);
    classGen = bytecodeEditor.getMy_classGen();
    fJavaClass = bytecodeEditor.getMy_javaClass();
  }

  /**
   * @return the editor for the current bytecode document
   */
  public BytecodeEditor getEditor() {
    return bytecodeEditor;
  }

  /**
   * @return <code>true</code> when the document change listener has already
   * been added to the document
   */
  public boolean isListenerAdded() {
    return !getDocumentListeners().isEmpty();
  }
}
