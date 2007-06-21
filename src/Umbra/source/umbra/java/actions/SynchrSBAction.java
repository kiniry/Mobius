/*
 * Created on 2005-07-20
 */
package umbra.java.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraException;
import umbra.UmbraHelper;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;

/**
 * This class defines an action of synchronization positions
 * form source code to bytecode. It is available with the standard
 * Java editor.
 *
 * @see DocumentProvider
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class SynchrSBAction implements IEditorActionDelegate {

  /**
   * The editor of the Java source code.
   */
  private CompilationUnitEditor my_editor;

  /**
   * The method sets the internal Java source code editor attribute.
   *
   * @param an_action the action which triggered the change of the editor
   * @param a_java_editor the new Java source code editor to be associated with
   * the action
   */
  public final void setActiveEditor(final IAction an_action,
                                    final IEditorPart a_java_editor) {
    my_editor = (CompilationUnitEditor)a_java_editor;
  }

  /**
   * This method handles the action of the syncronisation between the
   * source code and the bytecode i.e. it takes the selection in
   * the source code and shows the corresponding selection in the
   * bytecode.
   *
   * @param an_action the action that triggered the operation
   */
  public final void run(final IAction an_action) {
    final ITextSelection selection = (ITextSelection)my_editor.
                    getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final IPath active = ((FileEditorInput)my_editor.getEditorInput()).
                        getFile().getFullPath();
    final int lind = active.toOSString().lastIndexOf(UmbraHelper.JAVA_EXTENSION);
    if (lind == -1) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                  "Bytecode", "This is not a \"" +
                  UmbraHelper.JAVA_EXTENSION + "\" file");
      return;
    }
    IFile file;
    try {
      file = getClassFileForJavaFile(active);
    } catch (UmbraException e1) {
      return;
    }
    final FileEditorInput input = new FileEditorInput(file);
    try {
      final BytecodeEditor bcEditor = (BytecodeEditor)my_editor.getSite().
                           getPage().openEditor(input,
                            "umbra.BytecodeEditor",
                            true);
      if (bcEditor.isSaveOnCloseNeeded()) {
        MessageDialog.openWarning(my_editor.getSite().getShell(),
                      "Bytecode",
                      "The Bytecode editor needs being " +
                      "refreshed!");
        return;
      }
      final BytecodeDocument bDoc = ((BytecodeDocument)bcEditor.
                        getDocumentProvider().
                        getDocument(input));
      bDoc.synchronizeSB(off, bcEditor);
    } catch (PartInitException e) {
      e.printStackTrace();
    }
  }

  /**
   * This method gives the <code>IFile</code> with the bytecode that
   * corresponds to the file pointed out by the parameter
   * <code>a_java_path</code>. The method actually adds up the local error
   * handling code to an invocation of {@ref UmbraHelper.getClassFileName}.
   *
   * @param a_java_path a path for a file with a Java source code
   * @return the corresponding bytecode file
   * @throws UmbraException in case the file does not exist or
   */
  private IFile getClassFileForJavaFile(final IPath a_java_path)
    throws UmbraException {
    final String fname = UmbraHelper.replaceLast(a_java_path.toOSString(),
                  UmbraHelper.JAVA_EXTENSION, UmbraHelper.CLASS_EXTENSION);
    final IFile filel = ((FileEditorInput)my_editor.getEditorInput()).
            getFile();
    IFile file = null;
    try {
      file = UmbraHelper.getClassFileFile(filel, my_editor);
      if (!file.exists()) {
        MessageDialog.openError(my_editor.getSite().getShell(),
                    "Bytecode",
                    "File " + fname + " not found");
        throw new UmbraException();
      }
    } catch (JavaModelException e1) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                              "Bytecode",
                              "The current project has no classfile output " +
                              "location configured.");
      throw new UmbraException();
    }
    return file;
  }

  /**
   * Currently, does nothing.
   *
   * @param an_action see {@ref IActionDelegate#selectionChanged(IAction,
   *                       ISelection)}
   * @param a_selection see {@ref IActionDelegate#selectionChanged(IAction,
   *                       ISelection)}
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }

}
