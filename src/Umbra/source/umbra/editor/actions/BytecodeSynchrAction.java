package umbra.editor.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import umbra.editor.BytecodeDocument;

/**
 * This class defines action of synchronization bytecode
 * position with appropriate point in source code.
 *
 * @see BytecodeDocument
 * @author Wojtek Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeSynchrAction extends Action {

  /**
   * The current bytecode editor for which the action takes place.
   */
  private AbstractTextEditor editor;

  /**
   * The constructor of the action. It only registers the name of the
   * action in the eclipse environment.
   */
  public BytecodeSynchrAction() {
    super("Synchronize");
  }

  /**
   * This method sets the bytecode editor for which the
   * synchronization action will be executed.
   *
   * @param the bytecode editor for which the action will be executed
   */
  public void setActiveEditor(IEditorPart targetEditor) {
    editor = (AbstractTextEditor)targetEditor;
  }

  /**
   * This method consults the current selection, extracts the
   * offset of the selection and shows the related Java source
   * code document with the
   */
  public void run() {
    ITextSelection selection = (ITextSelection)editor.
                    getSelectionProvider().getSelection();
    int off = selection.getOffset();
    BytecodeDocument bDoc = (BytecodeDocument)editor.
                    getDocumentProvider().
                    getDocument(editor.getEditorInput());
    bDoc.synchronizeBS(off);
  }
}
