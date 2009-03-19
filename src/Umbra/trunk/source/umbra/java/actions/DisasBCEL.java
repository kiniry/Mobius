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


import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeDocumentProvider;
import umbra.editor.BytecodeEditor;
import umbra.editor.ColorModeContainer;
import umbra.editor.parsing.BytecodePartitionScanner;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.GUIMessages;

/**
 * This class defines the action related to Java source editor.
 * Its execution causes generating new related byte code file
 * in a new editor window.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
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
  public void run(final IAction an_action) {
    if (checkIfSaveNeeded()) return;
    if (checkJavaExtension()) return;
    final IFile jFile = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    try {
      FileNames.getClassFileFile(jFile, my_editor);
    } catch (JavaModelException e) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                              GUIMessages.DISAS_MESSAGE_TITLE,
                              GUIMessages.DISAS_CLASSFILEOUTPUT_PROBLEMS);
      return;
    }
    try {
      openBCodeEditorForJavaFile(jFile);
    } catch (JavaModelException e) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                                GUIMessages.DISAS_MESSAGE_TITLE,
                                GUIMessages.DISAS_CLASSFILEOUTPUT_PROBLEMS);
    } catch (PartInitException e) {
      MessageDialog.openError(my_editor.getSite().getShell(),
                                GUIMessages.DISAS_MESSAGE_TITLE,
                                GUIMessages.DISAS_EDITOR_PROBLEMS);
    } catch (ClassNotFoundException e) {
      messageProblemsWithLoading(jFile.getLocation());
    }
  }

  /**
   * This method opens a byte code editor for the given file that corresponds
   * to a Java resource. It figures out the name of the .btc file and opens
   * a byte code editor for this file. Subsequently it retrieves the
   * corresponding document and does the refresh of the byte code contained
   * in the document. This operation generates the textual content of the
   * document. Next the current method regenerates the colouring of the document
   * so that the document is not gray. At last the fresh content of the
   * document is saved to the .btc file on disc
   *
   * @param a_jfile the file with a path to the Java resource
   * @return the path of the class file from which the textual representation
   *   was generated
   * @throws PartInitException in case the byte code editor cannot be open
   * @throws JavaModelException in case the current project has no class file
   *   output location set
   * @throws ClassNotFoundException in case the class file for the given
   *   Java file cannot be found
   */
  protected IPath openBCodeEditorForJavaFile(final IFile a_jfile)
    throws PartInitException,
           JavaModelException, ClassNotFoundException {
    IPath cpath;
    final IWorkbenchPage page = my_editor.getEditorSite().getPage();
    final IFile btcFile = FileNames.getBTCFileName(a_jfile);
    final FileEditorInput input = new FileEditorInput(btcFile);
    BytecodeEditor bc_editor;
    bc_editor = (BytecodeEditor) (page.openEditor(input,
                           EclipseIdentifiers.BYTECODE_EDITOR_CLASS, false));
    bc_editor.setRelatedEditor(my_editor);
    final BytecodeDocumentProvider bdp = (BytecodeDocumentProvider)bc_editor.
      getDocumentProvider();
    final BytecodeDocument doc = (BytecodeDocument)bdp.getDocument(input);
                                   // this doc is empty when there is no .btc
                                   // file or contains the content of the file
    cpath = FileNames.getClassFileFile(a_jfile, my_editor).getFullPath();
    doc.getModel().initModTable();
    try {
      bc_editor.refreshBytecode(cpath, doc,
                                null, null); //this works on the doc
      openEditorAndDisassemble(page, bc_editor, input, doc);
      bdp.saveDocument(null, input, doc, true);
    } catch (CoreException e) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
        GUIMessages.DISAS_MESSAGE_TITLE,
        GUIMessages.substitute(GUIMessages.DISAS_SAVING_PROBLEMS,
                               input.getPath().toString()));
    }
    return cpath;
  }

  /**
   * This method opens a warning dialog which informs that there are problems
   * with loading a class file for the given source code file.
   *
   * @param a_path the path to Java source code
   */
  protected void messageProblemsWithLoading(final IPath a_path) {
    MessageDialog.openWarning(my_editor.getSite().getShell(),
      GUIMessages.DISAS_MESSAGE_TITLE,
      GUIMessages.substitute(GUIMessages.DISAS_LOADFORSOURCE_PROBLEM,
                             a_path.toString()));
  }

  /**
   * This method checks if the initial conditions for generation of bytecode
   * textual representation are met. These conditions are: the Java source
   * code is saved and the Java source code file ends with .java.
   *
   * @return <code>true</code> in case one of the conditions is not met,
   *   <code>false</code> in case the initial conditions are met
   */
  protected boolean checkInitialSavingConditions() {
    if (checkIfSaveNeeded()) return true;
    if (checkJavaExtension()) return true;
    return false;
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
        lastIndexOf(FileNames.JAVA_EXTENSION) == -1) {
      MessageDialog.openInformation(my_editor.getSite().getShell(),
                      GUIMessages.DISAS_MESSAGE_TITLE,
                      GUIMessages.substitute(GUIMessages.INVALID_EXTENSION,
                                             FileNames.JAVA_EXTENSION));
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
                    GUIMessages.DISAS_MESSAGE_TITLE,
                    GUIMessages.SAVE_BYTECODE_FIRST);
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
    ColorModeContainer.classKnown();
    a_doc.setDocumentPartitioner(IDocumentExtension3.DEFAULT_PARTITIONING,
                                 null);
    final IDocumentPartitioner partitioner =
      new FastPartitioner(
        new BytecodePartitionScanner(),
        an_editor.getConfiguration().getConfiguredContentTypes(null));
    partitioner.connect(a_doc);
    a_doc.setDocumentPartitioner(IDocumentExtension3.DEFAULT_PARTITIONING,
                                 partitioner);
    an_editor.setDocument(a_doc);
    an_editor.renewConfiguration(a_doc);
    an_editor.setRelation(my_editor);
    a_page.bringToTop(an_editor);
    ColorModeContainer.classUnknown();
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
  public void setActiveEditor(final IAction an_action,
                                    final IEditorPart a_target_editor) {
    my_editor = (CompilationUnitEditor)a_target_editor;
  }

  /**
   * Returns the editor associated with the action.
   *
   * @return the editor associated with the action
   */
  protected CompilationUnitEditor getEditor() {
    return my_editor;
  }

}
