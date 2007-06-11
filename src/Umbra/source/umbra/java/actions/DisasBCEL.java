/*
 * Created on 2005-04-21
 *
 */
package umbra.java.actions;

import java.io.IOException;

import org.apache.bcel.classfile.JavaClass;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

import umbra.UmbraHelper;
import umbra.editor.BytecodeEditor;
import umbra.editor.Composition;

/**
 * This class defines the action related to Java source editor.
 * Its execution causes generating new related bytecode file
 * in a new editor window.
 *
 * @author BYTECODE team
 */

public class DisasBCEL implements IEditorActionDelegate {

  /**
   * The editor of a Java file for which the bytecode file is
   * generated.
   */
  private CompilationUnitEditor editor;

  /**
   * Finds JavaClass structure related to the current Java
   * source. Generates new bytecode from it and displays
   * it in a new bytecode editor window.
   *
   * @param see the IActionDelegate.run(IAction)
   */
  public void run(IAction action) {
    IPath active = ((FileEditorInput)editor.
        getEditorInput()).getFile().getFullPath();
    if (editor.isSaveOnCloseNeeded()) {
      MessageDialog.openWarning(editor.getSite().getShell(),
                    UmbraHelper.DISAS_MESSAGE_TITLE,
                    UmbraHelper.DISAS_SAVE_BYTECODE_FIRST);
      return;
    }
    int lind = active.toOSString().lastIndexOf(UmbraHelper.JAVA_EXTENSION);
    if (lind == -1) {
      MessageDialog.openInformation(editor.getSite().getShell(),
                      UmbraHelper.DISAS_MESSAGE_TITLE,
                      UmbraHelper.INVALID_EXTENSION.
                      replaceAll(UmbraHelper.SUBSTITUTE,
                           UmbraHelper.JAVA_EXTENSION));
    } else {
      try {
        IFile filel = ((FileEditorInput)editor.getEditorInput()).
                             getFile();
        IFile file = UmbraHelper.getClassFileName(filel, editor);
        FileEditorInput input = new FileEditorInput(file);
        IWorkbenchPage page = editor.getEditorSite().getPage();
        BytecodeEditor bcEditor = (BytecodeEditor)page.openEditor(input,
                           UmbraHelper.BYTECODE_EDITOR_CLASS, true);
        bcEditor.refreshBytecode(active, null, null);
        input = new FileEditorInput(file);
        JavaClass jc = bcEditor.getJavaClass();
        Composition.startDisas();
        page.closeEditor(bcEditor, true);
        bcEditor = (BytecodeEditor)page.openEditor(input,
                          UmbraHelper.BYTECODE_EDITOR_CLASS, true);
        page.bringToTop(bcEditor);
        bcEditor.setRelation((AbstractDecoratedTextEditor)editor, jc);
        Composition.stopDisas();
      } catch (CoreException e) {
        e.printStackTrace();
      } catch (ClassNotFoundException e) {
        e.printStackTrace();
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
  }

  /**
   * Currently, does nothing.
   */
  public void selectionChanged(IAction action, ISelection selection) {
  }

  /**
   * It sets the editor with the Java source code.
   */
  public void setActiveEditor(IAction action, IEditorPart targetEditor) {
    editor = (CompilationUnitEditor)targetEditor;
  }

}
