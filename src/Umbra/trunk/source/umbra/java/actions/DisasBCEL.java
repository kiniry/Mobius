/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.java.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeDocumentProvider;
import umbra.editor.BytecodeEditor;
import umbra.editor.Composition;
import umbra.editor.parsing.BytecodePartitionScanner;

/**
 * This class defines the action related to Java source editor.
 * Its execution causes generating new related byte code file
 * in a new editor window.
 *
 * @author BYTECODE team (contact alx@mimuw.edu.pl)
 * @version a-01
 */

public class DisasBCEL implements IEditorActionDelegate {

  /**
   * The editor of a Java file for which the byte code file is
   * generated.
   */
  private CompilationUnitEditor my_editor;

  /**
   * Finds {@link org.apache.bcel.classfile.JavaClass} structure related to the
   * current Java source code. Generates new byte code from it and displays
   * it in a new byte code editor window.
   *
   * @param an_action see the IActionDelegate.run(IAction)
   * @see org.eclipse.ui.IActionDelegate#run(IAction)
   */
  public final void run(final IAction an_action) {
    if (checkIfSaveNeeded()) return;
    if (checkJavaExtension()) return;
    final IFile jFile = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    IPath cpath = null;
    try {
      cpath = openBCodeEditorForJavaFile(jFile);
    } catch (JavaModelException e) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
                                UmbraHelper.DISAS_MESSAGE_TITLE,
                                UmbraHelper.DISAS_CLASSFILEOUTPUT_PROBLEMS);
    } catch (PartInitException e) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
                                UmbraHelper.DISAS_MESSAGE_TITLE,
                                UmbraHelper.DISAS_EDITOR_PROBLEMS);
    } catch (ClassNotFoundException e) {
      messageClassNotFound(cpath);
    } catch (CoreException e) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
                                UmbraHelper.DISAS_MESSAGE_TITLE,
                                UmbraHelper.DISAS_SAVING_PROBLEMS);
    }
  }

  /**
   * @param jFile
   * @return
   * @throws PartInitException
   * @throws JavaModelException
   * @throws ClassNotFoundException
   * @throws CoreException
   */
  private IPath openBCodeEditorForJavaFile(final IFile jFile)
    throws PartInitException,
           JavaModelException, ClassNotFoundException, CoreException {
    IPath cpath;
    final IWorkbenchPage page = my_editor.getEditorSite().getPage();
    final IFile btcFile = UmbraHelper.getBTCFileName(jFile, my_editor);
    final FileEditorInput input = new FileEditorInput(btcFile);
    BytecodeEditor bc_editor;
    bc_editor = (BytecodeEditor) (page.openEditor(input,
                           UmbraHelper.BYTECODE_EDITOR_CLASS, false));
    bc_editor.setRelatedEditor(my_editor);
    final BytecodeDocumentProvider bdp = (BytecodeDocumentProvider)bc_editor.
      getDocumentProvider();
    final BytecodeDocument doc = (BytecodeDocument)bdp.getDocument(input);
                                   // this doc is empty when there is no .btc
                                   // file or contains the content of the file
    cpath = UmbraHelper.getClassFileFile(jFile, my_editor).getFullPath();
    doc.initModTable();
    bc_editor.refreshBytecode(cpath, doc,
                                null, null); //this works on the doc
    openEditorAndDisassemble(page, bc_editor, input, doc);
    bdp.saveDocument(null, input, doc, true);
    return cpath;
  }

  /**
   * This method opens a warning dialog with the information that the given
   * path does not exist.
   *
   * @param a_path the path which does not exist
   */
  private void messageClassNotFound(final IPath a_path) {
    MessageDialog.openWarning(my_editor.getSite().getShell(),
                              UmbraHelper.DISAS_MESSAGE_TITLE,
                              UmbraHelper.DISAS_PATH_DOES_NOT_EXIST +
                              " (" + a_path.toString() + ")");
  }

  /**
   * This method checks if the source code editor edits .java file.
   * In case the file is not a .java file a popup
   * with appropriate message is shown.
   *
   * @return <code>true</code> if the file is not a .java file,
   *   <code>false</code> otherwise
   */
  private boolean checkJavaExtension() {
    final IPath active = ((FileEditorInput) (my_editor.getEditorInput())).
    getFile().getFullPath();
    if (active.toPortableString().
        lastIndexOf(UmbraHelper.JAVA_EXTENSION) == -1) {
      MessageDialog.openInformation(my_editor.getSite().getShell(),
                      UmbraHelper.DISAS_MESSAGE_TITLE,
                      UmbraHelper.INVALID_EXTENSION.
                      replaceAll(UmbraHelper.SUBSTITUTE,
                           UmbraHelper.JAVA_EXTENSION));
      return true;
    }  else
      return false;
  }

  /**
   * This method checks if the source code editor must be saved before an
   * action can be performed. In case the editor must be saved a popup
   * with appropriate message is shown.
   *
   * @return <code>true</code> when the save is needed, <code>false</code>
   * otherwise
   */
  private boolean checkIfSaveNeeded() {
    if (my_editor.isSaveOnCloseNeeded()) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
                    UmbraHelper.DISAS_MESSAGE_TITLE,
                    UmbraHelper.DISAS_SAVE_BYTECODE_FIRST);
      return true;
    }
    return false;
  }

  /**
   * This method changes the colouring mode of a previously opened editor.
   * Now, the content of the editor is coloured with the current colouring
   * style instead of the gray style which is the default for documents with
   * no connection with a class file.
   *
   * @param a_page a workbench page in which the new editor is reconfigured
   * @param an_editor the editor to change the colouring for
   * @param an_input an input which will be presented in the editor
   * @param a_doc a document where the BCEL and BMLlib connection is already set
   */
  private void openEditorAndDisassemble(final IWorkbenchPage a_page,
                                        final BytecodeEditor an_editor,
                                        final FileEditorInput an_input,
                                        final BytecodeDocument a_doc) {
    Composition.startDisas();
    a_doc.setDocumentPartitioner(IDocumentExtension3.DEFAULT_PARTITIONING,
                                 null);
    final IDocumentPartitioner partitioner =
      new FastPartitioner(
        new BytecodePartitionScanner(),
        new String[] {
          BytecodePartitionScanner.TAG,
          BytecodePartitionScanner.HEAD,
          BytecodePartitionScanner.THROWS});
    partitioner.connect(a_doc);
    a_doc.setDocumentPartitioner(IDocumentExtension3.DEFAULT_PARTITIONING,
                                 partitioner);
    an_editor.renewConfiguration(a_doc);
    an_editor.setRelation(my_editor);
    a_page.bringToTop(an_editor);
    Composition.stopDisas();
  }

  /**
   * Currently, does nothing.
   *
   * @param an_action see {@link
   *   org.eclipse.ui.IActionDelegate#selectionChanged(IAction,ISelection)}
   * @param a_selection see {@link
   *   org.eclipse.ui.IActionDelegate#selectionChanged(IAction,ISelection)}
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }

  /**
   * It sets the editor with the Java source code.
   *
   * @param an_action see {@link
   *   org.eclipse.ui.IEditorActionDelegate#setActiveEditor(IAction,
   *   IEditorPart)}
   * @param a_target_editor the new editor to be active for the action
   */
  public final void setActiveEditor(final IAction an_action,
                                    final IEditorPart a_target_editor) {
    my_editor = (CompilationUnitEditor)a_target_editor;
  }

}
