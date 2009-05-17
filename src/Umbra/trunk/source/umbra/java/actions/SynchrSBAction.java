/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.java.actions;

import java.io.InputStream;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import annot.bcclass.BCClass;

import umbra.UmbraPlugin;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeDocumentProvider;
import umbra.editor.BytecodeEditor;
import umbra.editor.DocumentSynchroniser;
import umbra.lib.BMLParsing;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraSynchronisationException;

/**
 * This class defines an action of synchronization positions
 * form source code to bytecode. It is available with the standard
 * Java editor.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Wojciech Tyczyński (wt237242@students.mimuw.edu.pl)
 * @version a-01
 */
public class SynchrSBAction implements IEditorActionDelegate {

  /**
   * The editor of the Java source code.
   */
  private CompilationUnitEditor my_editor;

  /**
   * This is an object which handles the calculations of the synchronisation
   * positions.
   */
  private DocumentSynchroniser my_synchroniser;

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
   * This method handles the action of the synchronisation between the
   * source code and the byte code i.e. it takes the selection in
   * the source code and shows the corresponding selection in the
   * byte code.
   *
   * @param an_action the action that triggered the operation
   */
  public final void run(final IAction an_action) {
    UmbraPlugin.LOG.println("synchrSBAction on " + this);
    final ITextSelection selection = (ITextSelection) my_editor.
                    getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final IFile activef = ((FileEditorInput)my_editor.getEditorInput()).
                                                      getFile();
    final IPath active = activef.getFullPath();
    final int lind = active.toPortableString().
                            lastIndexOf(FileNames.JAVA_EXTENSION);
    if (lind == -1) {
      System.out.println("lind == -1");
      MessageDialog.openError(my_editor.getSite().getShell(),
        GUIMessages.SYNCH_MESSAGE_TITLE,
        GUIMessages.substitute(GUIMessages.INVALID_EXTENSION,
                               FileNames.JAVA_EXTENSION));
      return;
    }

    final IFile file = FileNames.getBTCFileName(activef);
    System.out.println("BTC file = " + file);
    final FileEditorInput input = new FileEditorInput(file);
    try {
      final BytecodeEditor bcEditor = (BytecodeEditor)my_editor.getSite().
                           getPage().openEditor(input,
                            EclipseIdentifiers.BYTECODE_EDITOR_CLASS,
                            true);
      System.out.println("bcEditor = " + bcEditor);
      if (bcEditor.isSaveOnCloseNeeded()) {
        MessageDialog.openWarning(my_editor.getSite().getShell(),
          GUIMessages.SYNCH_MESSAGE_TITLE, GUIMessages.REFRESH_REQUIRED);
        return;
      }
      final BytecodeDocument bDoc = ((BytecodeDocument)bcEditor.
                        getDocumentProvider().
                        getDocument(input));
      System.out.println("bDoc = " + bDoc.toString());

      /* wt237242@students.mimuw.edu.pl */
      try {
        bcEditor.setRelatedEditor(my_editor);
        final BytecodeDocumentProvider bdp = 
          (BytecodeDocumentProvider)bcEditor.getDocumentProvider();
        final BytecodeDocument doc = (BytecodeDocument)bdp.getDocument(input);
          // this doc is empty when there is no .btc
          // file or contains the content of the file
        final IPath cpath = FileNames.getClassFileFile(activef, my_editor).
          getFullPath();
        doc.getModel().initModTable();
        bcEditor.refreshBytecode(cpath, doc, null, null);
      } catch (Exception e) {
        e.printStackTrace();
      }

      synchronizeWithMessages(off, bDoc);
    } catch (PartInitException e) {
      e.printStackTrace();
      MessageDialog.openError(my_editor.getSite().getShell(),
        GUIMessages.SYNCH_MESSAGE_TITLE, GUIMessages.DISAS_EDITOR_PROBLEMS);
    }
  }

  /**
   * This method performs the synchronisation of the byte code document for
   * the given position in the source code document. This method additionally
   * pops up all the necessary messages in case exceptions are raised.
   *
   * @param an_offset a position in the source code editor. Lines in related
   *   byte code editor containing the line with this postion will
   *   be highlighted
   * @param a_bcode_doc the byte code document to synchronise
   */
  private void synchronizeWithMessages(final int an_offset,
                                       final BytecodeDocument a_bcode_doc) {
    System.out.println("synchronizeWithMessages("+an_offset+","+a_bcode_doc+")");
    final Shell parent = my_editor.getSite().getShell();
    try {
      getDocSynch(a_bcode_doc).synchronizeSB(an_offset, my_editor);
    } catch (UmbraLocationException e) {
      e.printStackTrace();
      GUIMessages.messageWrongLocation(parent, GUIMessages.SYNCH_MESSAGE_TITLE,
                                       e);
    } catch (UmbraSynchronisationException e) {
      e.printStackTrace();
      MessageDialog.openError(parent, GUIMessages.SYNCH_MESSAGE_TITLE,
                              GUIMessages.WRONG_SYNCHRONISATION_MSG);
    } catch (JavaModelException e) {
      e.printStackTrace();
      MessageDialog.openError(parent, GUIMessages.SYNCH_MESSAGE_TITLE,
                              GUIMessages.WRONG_JAVAACCESS_MSG);
    }
  }

  /**
   * Currently, does nothing.
   *
   * @param an_action see
   *   {@link org.eclipse.ui.IActionDelegate#selectionChanged(IAction,
   *          ISelection)}
   * @param a_selection see
   *   {@link org.eclipse.ui.IActionDelegate#selectionChanged(IAction,
   *          ISelection)}
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }

  /**
   * This method lazily provides the object which performs the synchronisation
   * operations.
   *
   * @param a_doc a byte code document for which the synchronisation is
   *   performed
   * @return a {@link DocumentSynchroniser} which performs the synchronisation
   *   operations
   */
  private DocumentSynchroniser getDocSynch(final BytecodeDocument a_doc) {
    final CompilationUnitEditor jsceditor = my_editor;
    my_synchroniser = new DocumentSynchroniser(a_doc,
                            jsceditor.getDocumentProvider().
                            getDocument(jsceditor.getEditorInput()));
    return my_synchroniser;
  }
}
