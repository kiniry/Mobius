/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.java.actions;

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
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeEditor;
import umbra.editor.Composition;

/**
 * This class defines the action related to Java source editor.
 * Its execution causes generating new related bytecode file
 * in a new editor window.
 *
 * @author BYTECODE team (contact alx@mimuw.edu.pl)
 * @version a-01
 */

public class DisasBCEL implements IEditorActionDelegate {

  /**
   * The editor of a Java file for which the bytecode file is
   * generated.
   */
  private CompilationUnitEditor my_editor;

  /**
   * Finds {@ref JavaClass} structure related to the current Java
   * source code. Generates new bytecode from it and displays
   * it in a new bytecode editor window.
   *
   * @param an_action see the IActionDelegate.run(IAction)
   * @see org.eclipse.ui.IActionDelegate#run(IAction)
   */
  public final void run(final IAction an_action) {
    final IPath active = ((FileEditorInput) (my_editor.getEditorInput())).
                                                     getFile().getFullPath();
    if (my_editor.isSaveOnCloseNeeded()) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
                    UmbraHelper.DISAS_MESSAGE_TITLE,
                    UmbraHelper.DISAS_SAVE_BYTECODE_FIRST);
      return;
    }
    if (active.toPortableString().
        lastIndexOf(UmbraHelper.JAVA_EXTENSION) == -1) {
      MessageDialog.openInformation(my_editor.getSite().getShell(),
                      UmbraHelper.DISAS_MESSAGE_TITLE,
                      UmbraHelper.INVALID_EXTENSION.
                      replaceAll(UmbraHelper.SUBSTITUTE,
                           UmbraHelper.JAVA_EXTENSION));
      return;
    }
    final IFile jFile = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    final IWorkbenchPage page = my_editor.getEditorSite().getPage();
    try {
      final IFile btcFile = UmbraHelper.getBTCFileName(jFile, my_editor);
      final FileEditorInput input = new FileEditorInput(btcFile);
      final BytecodeEditor bc_editor = (BytecodeEditor) (page.openEditor(input,
                           UmbraHelper.BYTECODE_EDITOR_CLASS, true));
      bc_editor.setRelatedEditor(my_editor);
      bc_editor.refreshBytecode(UmbraHelper.getClassFileFile(jFile, my_editor).
                                            getFullPath(),
                                null, null);
      final JavaClass jc = bc_editor.getJavaClass();
      page.closeEditor(bc_editor, true);
      openEditorAndDisassemble(page, input, jc);
    } catch (CoreException e) {
      e.printStackTrace();
    } catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
  }

  /**
   * This method opens previously closed editor so that the content of the
   * editor is coloured with the current colouring style.
   *
   * @param a_page a workbench page in which the new editor is to be reopend
   * @param an_input an input wchich will be presented in the editor
   * @param a_jclass a BCEL Java class structure to be associated with the
   *                 editor
   * @throws PartInitException if the editor could not be created or initialized
   */
  private void openEditorAndDisassemble(final IWorkbenchPage a_page,
                                        final FileEditorInput an_input,
                                        final JavaClass a_jclass)
    throws PartInitException {
    Composition.startDisas();
    final BytecodeEditor a_beditor = (BytecodeEditor)a_page.openEditor(an_input,
                        UmbraHelper.BYTECODE_EDITOR_CLASS, true);
    a_page.bringToTop(a_beditor);
    a_beditor.setRelation(my_editor, a_jclass);
    Composition.stopDisas();
  }

  /**
   * Currently, does nothing.
   *
   * @param an_action see {@ref IActionDelegate#selectionChanged(IAction,
   *                   ISelection)}
   * @param a_selection see {@ref IActionDelegate#selectionChanged(IAction,
   *                       ISelection)}
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }

  /**
   * It sets the editor with the Java source code.
   *
   * @param an_action see {@ref IEditorActionDelegate#setActiveEditor(IAction,
   *                    IEditorPart)}
   * @param a_target_editor the new editor to be active for the action
   */
  public final void setActiveEditor(final IAction an_action,
                                    final IEditorPart a_target_editor) {
    my_editor = (CompilationUnitEditor)a_target_editor;
  }

}
