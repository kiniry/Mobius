/*
 * Created on 2005-05-03
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package umbra.editor;

import java.net.MalformedURLException;
import java.net.URL;

import org.apache.bcel.classfile.JavaClass;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorActionBarContributor;
import org.eclipse.ui.texteditor.AbstractTextEditor;

import umbra.UmbraPlugin;
import umbra.editor.actions.BytecodeCombineAction;
import umbra.editor.actions.BytecodeColorAction;
import umbra.editor.actions.BytecodeRebuildAction;
import umbra.editor.actions.BytecodeRefreshAction;
import umbra.editor.actions.BytecodeRestoreAction;
import umbra.editor.actions.BytecodeSynchrAction;


/**
 * This is managing class that adds actions to workbench menus and toolbars
 * for a bytecode editor. They appear when the editor is active. These actions
 * are in particular: rebuild, refresh, combine, restore from history,
 * synchronize the position of the cursor between the bytecode and the Java
 * code, color change and check of the syntax correctness.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeEditorContributor extends EditorActionBarContributor {

  /**
   * TODO
   */
  private BytecodeContribution bytecodeContribution;

  /**
   * The action to change the color mode to the next one.
   */
  private BytecodeColorAction actionPlus;

  /**
   * The action to change the color mode to the previous one.
   */
  private BytecodeColorAction actionMinus;

  /**
   * The action to refresh the content of the current bytecode editor.
   */
  private BytecodeRefreshAction refreshAction;

  /**
   * TODO
   */
  private BytecodeRebuildAction rebuildAction;

  /**
   * The action to combine the modifications from the source code editor
   * and from the bytecode editor.
   */
  private BytecodeCombineAction combineAction;

  /**
   * The action to restore one of the history snapshots that
   * were stored before.
   */
  private BytecodeRestoreAction restoreAction;

  /**
   * The action to synchronize the position in the bytecode file with
   * the corresponding position in the source code file.
   */
  private BytecodeSynchrAction synchrAction;

  /**
   * The constructor is executed when the editor is started.
   * It includes creating all actions and provide them with their icons.
   *
   * @throws MalformedURLException
   */
  public BytecodeEditorContributor() {
    super();
    final int mod = Composition.getMod();
    bytecodeContribution = BytecodeContribution.newItem();
    bytecodeContribution.addEditorContributor(this);
    actionPlus = new BytecodeColorAction(this, 1, mod);
    actionMinus = new BytecodeColorAction(this,
                         IColorValues.MODELS.length - 2,
                         mod);
    refreshAction = new BytecodeRefreshAction(this, bytecodeContribution);
    rebuildAction = new BytecodeRebuildAction(this);
    combineAction = new BytecodeCombineAction(this, bytecodeContribution);
    restoreAction = new BytecodeRestoreAction(this, bytecodeContribution);
    synchrAction = new BytecodeSynchrAction();
    final URL installURL = UmbraPlugin.getDefault().getBundle().getEntry("/");
    try {
      ImageDescriptor iconRight;
      ImageDescriptor iconLeft;
      ImageDescriptor refreshIcon;
      ImageDescriptor rebuildIcon;
      ImageDescriptor combineIcon;
      ImageDescriptor restoreIcon;
      ImageDescriptor synchrIcon;
      final URL url = new URL(installURL, "icons/change_color_backward.gif");
      System.out.println(url.toExternalForm());
      iconRight = ImageDescriptor.
        createFromURL(url);
      iconLeft = ImageDescriptor.
        createFromURL(new URL(installURL, "icons/change_color_forward.gif"));
      refreshIcon = ImageDescriptor.
        createFromURL(new URL(installURL, "icons/refresh.gif"));
      rebuildIcon = ImageDescriptor.
        createFromURL(new URL(installURL, "icons/rebuild_bytecode.gif"));
      combineIcon = ImageDescriptor.
        createFromURL(new URL(installURL, "icons/combine.gif"));
      restoreIcon = ImageDescriptor.
        createFromURL(new URL(installURL, "icons/restoreH.gif"));
      synchrIcon = ImageDescriptor.
        createFromURL(new URL(installURL, "icons/synchronize.gif"));
      actionPlus.setImageDescriptor(iconRight);
      actionMinus.setImageDescriptor(iconLeft);
      refreshAction.setImageDescriptor(refreshIcon);
      rebuildAction.setImageDescriptor(rebuildIcon);
      combineAction.setImageDescriptor(combineIcon);
      restoreAction.setImageDescriptor(restoreIcon);
      synchrAction.setImageDescriptor(synchrIcon);

    } catch (MalformedURLException e) {
      MessageDialog.openError(new Shell(),
          "Bytecode",
          "Improper bytecode icon on eclipse GUI reference (" +
          e.getMessage() + ")");
    }
    actionPlus.setToolTipText("Change color");
    actionMinus.setToolTipText("Change color");
    refreshAction.setToolTipText("Refresh");
    rebuildAction.setToolTipText("Rebuild");
    combineAction.setToolTipText("Combine");
    restoreAction.setToolTipText("Restore");
    synchrAction.setToolTipText("Synchronize");
  }

  /**
   * New buttons for the actions are added to the toolbar.
   */
  public final void contributeToToolBar(final IToolBarManager toolBarManager) {
    // Run super.
    super.contributeToToolBar(toolBarManager);
    // Test status line.
    toolBarManager.add(bytecodeContribution);
    toolBarManager.add(actionPlus);
    toolBarManager.add(actionMinus);
    toolBarManager.add(refreshAction);
    toolBarManager.add(rebuildAction);
    toolBarManager.add(combineAction);
    toolBarManager.add(restoreAction);
    toolBarManager.add(synchrAction);
  }

  /**
   * New items for the actions are added to the menu.
   *
   * @param menuManager TODO
   */
  public final void contributeToMenu(final IMenuManager menuManager) {
    // Run super.
    super.contributeToMenu(menuManager);
    final MenuManager bytecodeMenu = new MenuManager("Editor"); //$NON-NLS-1$
    menuManager.insertAfter("additions", bytecodeMenu); //$NON-NLS-1$
    bytecodeMenu.add(actionPlus);
    bytecodeMenu.add(actionMinus);
    bytecodeMenu.add(refreshAction);
    bytecodeMenu.add(rebuildAction);
    bytecodeMenu.add(combineAction);
    bytecodeMenu.add(restoreAction);
    bytecodeMenu.add(synchrAction);
  }

  /**
   * The current editor window is set as an attribute
   * (also for each action)
   *
   * @param editor  the current editor window
   */
  public final void setActiveEditor(final IEditorPart editor) {
    super.setActiveEditor(editor);
    bytecodeContribution.setActiveEditor(editor);
    actionPlus.setActiveEditor(editor);
    actionMinus.setActiveEditor(editor);
    refreshAction.setActiveEditor(editor);
    rebuildAction.setActiveEditor(editor);
    combineAction.setActiveEditor(editor);
    restoreAction.setActiveEditor(editor);
    synchrAction.setActiveEditor(editor);
  }

  /**
   * The same as {@ref #refreshEditor(IEditorPart, IEditorInput)}, but
   * the input is obtained from the current editor window.
   *
   * @see #refreshEditor(IEditorPart, IEditorInput)
   * @throws PartInitException if the new editor could not be created or
   *               initialized
   */
  public final void refreshEditor(final IEditorPart editor) throws PartInitException {
    final IEditorInput input = editor.getEditorInput();
    refreshEditor(editor, input);
  }

  /**
   * Saves all settings of the current editor (selection positions,
   * contributions, JavaClass structure, related editor). Then closes the
   * editor and opens a new one with the same settings and given input.
   *
   * @param editor current editor to be closed
   * @param input input file to be displayed in new editor
   * @throws PartInitException if the new editor could not be created or
   *    initialized
   */
  public final void refreshEditor(final IEditorPart editor,
                                  final IEditorInput input)
    throws PartInitException {
    final IWorkbenchPage page = editor.getEditorSite().getPage();
    final ITextSelection selection = (ITextSelection)((AbstractTextEditor)editor).getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final int len = selection.getLength();
    final CompilationUnitEditor related = ((BytecodeEditor)editor).getRelatedEditor();
    final JavaClass jc = ((BytecodeEditor)editor).getMy_javaClass();
    final boolean proper = (related != null);
    bytecodeContribution.survive();
    if (proper) Composition.startDisas();
    page.closeEditor(editor, true);
    final IEditorPart newEditor = page.openEditor(input,
                        "umbra.BytecodeEditor", true);
    ((BytecodeEditor) newEditor).setRelation(related, jc);
    final ISelection ns = new TextSelection(off, len);
    final ISelectionProvider sp = ((AbstractTextEditor)newEditor).
                          getSelectionProvider();
    sp.setSelection(ns);
    bytecodeContribution.reinit();
    if (proper) Composition.stopDisas();
  }

  /**
   * This method disables the synchronisation action in the editor.
   */
  public final void synchrDisable() {
    synchrAction.setEnabled(false);
  }

  /**
   * This method enables the synchronisation action in the editor.
   */
  public final void synchrEnable() {
    synchrAction.setEnabled(true);
  }

  /**
   * debugging helper
   *
  /*private void controlPrint(JavaClass jc, int i) {
    Method meth = jc.getMethods()[i];
    System.out.println(meth.getCode().toString());
  }*/

  /**
   * This returns the action ?that executes the refresh action.
   *
   * @return
   */
  public final BytecodeRefreshAction getRefreshAction() {
    return refreshAction;
  }
}
