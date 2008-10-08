/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;
import umbra.instructions.BytecodeController;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraMethodException;
import umbra.lib.UmbraRangeException;
import umbra.lib.UmbraSyntaxException;


/**
 * This is a class defining an action: save current byte code
 * editor window and re-generate byte code from the .class file.
 * This action is equivalent to the generation of the byte code again from the
 * Java code after saving binary file.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeRefreshAction extends BytecodeEditorAction {

  /**
   * This constructor creates the action to refresh the byte code editor.
   * It registers the name of the action and stores
   * locally the object which creates all the actions and which contributes
   * the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   *   the byte code plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   *   GUI by the byte code editor. This reference should be the same as in the
   *   parameter <code>a_contributor</code>.
   */
  public BytecodeRefreshAction(final BytecodeEditorContributor a_contributor,
                 final BytecodeContribution a_bytecode_contribution) {
    super(EclipseIdentifiers.REFRESH_ACTION_NAME, a_contributor,
          a_bytecode_contribution);
  }

  /**
   * This method sets the byte code editor for which the refresh action will
   * be executed. Except for the superclass functionality it sets the
   * refresh action to be active in case the editor is dirty.
   *
   * @param a_target_editor the byte code editor for which the action will be
   *    executed
   */
  public final void setActiveEditor(final IEditorPart a_target_editor) {
    super.setActiveEditor(a_target_editor);
    if (!getEditor().isDirty()) setEnabled(false);
  }

  /**
   * This method saves the editor content in the files .btc. and .class
   * associated with it and then creates a new input from the .class file.
   * Finally replaces content of the editor window with the newly generated
   * text. The general idea is that the current modifications are stored
   * in a file and then retrieved back to the editor to obtain a nicely
   * formatted presentation of the code.
   */
  public final void run() {
    final Shell parent = getEditor().getSite().getShell();
    final BytecodeEditor my_editor = getEditor();

    final int topvisible = my_editor.getVisibleRegion();
    my_editor.doSave(null);
    final FileEditorInput input = (FileEditorInput)my_editor.getEditorInput();
    final IFile file = input.getFile();
    try {
      final BytecodeEditor newEditor = doRefresh(my_editor, file);
      newEditor.setVisibleRegion(topvisible);
      setActiveEditor(newEditor);
    } catch (ClassNotFoundException e) {
      wrongPathToClassMessage(parent, getDescription(), file.toString());
    } catch (CoreException e) {
      wrongFileOperationMessage(parent, getDescription());
    } catch (UmbraRangeException e) {
      GUIMessages.exceededRangeInfo(new Shell(), e, "Byte code refreshing");
    } catch (UmbraSyntaxException e) {
      // TODO Auto-generated catch block
      e.printStackTrace(); 
    }
  }

  /**
   * This method does the actual job of refreshing the content of the byte
   * code editor with an already saved content of a class file. First, we
   * obtain the path to the class file. Then we store temporarily the
   * comments and information on the modified methods. Then we refresh
   * the byte code and the editor.
   *
   * @param the_editor the editor which is refreshed
   * @param a_file the .btc file the content of which is refreshed
   * @return the fresh editor
   * @throws ClassNotFoundException the class corresponding to the given file
   *   cannot be found
   * @throws CoreException a file operation on the byte code file did not
   *   succeed
   * @throws UmbraRangeException thrown in case a position has been reached
   *   which is outside the current document or when the textual representation
   *   has more methods than the internal one
   * @throws UmbraSyntaxException 
   */
  private BytecodeEditor doRefresh(final BytecodeEditor the_editor,
                               final IFile a_file)
    throws ClassNotFoundException,
           CoreException, UmbraRangeException, UmbraSyntaxException {
    final BytecodeEditorContributor a_contributor = getContributor();
    final IPath active = FileNames.getClassFileFileFor(a_file, the_editor,
                             FileNames.BYTECODE_EXTENSION).getFullPath();
    //memorise the current state of the session
    final BytecodeDocument doc = the_editor.getDocument();
    final BytecodeController model = doc.getModel();
    final String[] eolComments = model.getEOLComments();
    final String[] interlineComm = model.getInterlineComments();
    final boolean[] modified = model.getModified();
    the_editor.refreshBytecode(active, doc, eolComments, interlineComm);
    final BytecodeEditor newEditor;
    try {
      newEditor = a_contributor.refreshEditor(the_editor,
                                                      eolComments,
                                                      interlineComm);
    } catch (UmbraLocationException e) {
      throw new UmbraRangeException(e);
    } catch (UmbraMethodException e) {
      throw new UmbraRangeException(e);
    }
    newEditor.getDocument().getModel().setModified(modified);
    return newEditor;
  }
}
