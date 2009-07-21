/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
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
   * TODO.
   */
  private BytecodeContribution my_bcode_cntrbtn;

  /**
   * The action to change the color mode to the next one.
   */
  private BytecodeColorAction my_action_plus;

  /**
   * The action to change the color mode to the previous one.
   */
  private BytecodeColorAction my_action_minus;

  /**
   * The action to refresh the content of the current bytecode editor.
   */
  private BytecodeRefreshAction my_refresh_action;

  /**
   * TODO.
   */
  private BytecodeRebuildAction my_rebuild_action;

  /**
   * The action to combine the modifications from the source code editor
   * and from the bytecode editor.
   */
  private BytecodeCombineAction my_combine_action;

  /**
   * The action to restore one of the history snapshots that
   * were stored before.
   */
  private BytecodeRestoreAction my_restore_action;

  /**
   * The action to synchronize the position in the bytecode file with
   * the corresponding position in the source code file.
   */
  private BytecodeSynchrAction my_synchr_action;

  /**
   * The constructor is executed when the editor is started.
   * It includes creating all actions and provide them with their icons.
   *
   * @throws MalformedURLException TODO
   */
  public BytecodeEditorContributor() throws MalformedURLException {
    super();
    my_bcode_cntrbtn = BytecodeContribution.newItem();
    my_bcode_cntrbtn.addEditorContributor(this);
    my_refresh_action = new BytecodeRefreshAction(this, my_bcode_cntrbtn);
    my_rebuild_action = new BytecodeRebuildAction(this);
    my_combine_action = new BytecodeCombineAction(this, my_bcode_cntrbtn);
    my_restore_action = new BytecodeRestoreAction(this, my_bcode_cntrbtn);
    my_synchr_action = new BytecodeSynchrAction();
    final URL installURL = UmbraPlugin.getDefault().getBundle().getEntry("/");
    assignIcons(installURL);
    my_refresh_action.setToolTipText("Refresh");
    my_rebuild_action.setToolTipText("Rebuild");
    my_combine_action.setToolTipText("Combine");
    my_restore_action.setToolTipText("Restore");
    my_synchr_action.setToolTipText("Synchronize");
    setupColorActions(installURL, Composition.getMod());
  }

  /**
   * This method sets up all the actions which change the colouring style
   * of the editor.
   *
   * @param an_install_url the URL to the location of the Umbra plugin
   *        installation
   * @param a_mode the current colouring mode
   */
  private void setupColorActions(final URL an_install_url,
                                 final int a_mode) {
    my_action_plus = new BytecodeColorAction(this, 1, a_mode);
    // TODO: for some reason the second parameter was
    //       ColorValues.MODELS.length - 2,
    my_action_minus = new BytecodeColorAction(this, -1, a_mode);
    ImageDescriptor icon_right;
    ImageDescriptor icon_left;
    URL url;
    try {
      url = new URL(an_install_url, "icons/change_color_backward.gif");
      icon_right = ImageDescriptor.
        createFromURL(url);
      icon_left = ImageDescriptor.
        createFromURL(new URL(an_install_url,
                              "icons/change_color_forward.gif"));
      my_action_plus.setImageDescriptor(icon_right);
      my_action_minus.setImageDescriptor(icon_left);
    } catch (MalformedURLException e) {
      wrongIconMessage(e);
    }
    my_action_plus.setToolTipText("Change color");
    my_action_minus.setToolTipText("Change color");
  }

  /**
   * TODO.
   * @param an_install_url TODO
   */
  private void assignIcons(final URL an_install_url) {
    try {

      ImageDescriptor refresh_icon;
      ImageDescriptor rebuild_icon;
      ImageDescriptor combine_icon;
      ImageDescriptor restore_icon;
      ImageDescriptor synchr_icon;
      refresh_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/refresh.gif"));
      rebuild_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/rebuild_bytecode.gif"));
      combine_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/combine.gif"));
      restore_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/restoreH.gif"));
      synchr_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/synchronize.gif"));
      my_refresh_action.setImageDescriptor(refresh_icon);
      my_rebuild_action.setImageDescriptor(rebuild_icon);
      my_combine_action.setImageDescriptor(combine_icon);
      my_restore_action.setImageDescriptor(restore_icon);
      my_synchr_action.setImageDescriptor(synchr_icon);
    } catch (MalformedURLException e) {
      wrongIconMessage(e);
    }
  }

  /**
   * The method pops up a message which informs that something is wrong with
   * the paths to the Umbra icons.
   *
   * @param an_ex the exception for which the message should pop up
   */
  private void wrongIconMessage(final MalformedURLException an_ex) {
    MessageDialog.openError(new Shell(),
        "Bytecode",
        "Improper bytecode icon on eclipse GUI reference (" +
        an_ex.getMessage() + ")");
  }

  /**
   * New buttons for the actions are added to the toolbar. We call the
   * superclass method and add:
   * <ul>
   *   <li>the widget of the bytecode contribution</li>
   *   <li>two icons for changing the colouring style</li>
   *   <li>the refresh action icon</li>
   *   <li>the rebuild action icon</li>
   *   <li>the combine action icon</li>
   *   <li>the restore action icon</li>
   *   <li>the synchronisation icon</li>
   * </ul>
   * @param a_tbar_mngr the toolbar into which the widgets are added
   * @see EditorActionBarContributor#contributeToToolBar(IToolBarManager)
   */
  public final void contributeToToolBar(final IToolBarManager a_tbar_mngr) {
    // Run super.
    super.contributeToToolBar(a_tbar_mngr);
    // Test status line.
    a_tbar_mngr.add(my_bcode_cntrbtn);
    a_tbar_mngr.add(my_action_plus);
    a_tbar_mngr.add(my_action_minus);
    a_tbar_mngr.add(my_refresh_action);
    a_tbar_mngr.add(my_rebuild_action);
    a_tbar_mngr.add(my_combine_action);
    a_tbar_mngr.add(my_restore_action);
    a_tbar_mngr.add(my_synchr_action);
  }

  /**
   * New items for the actions are added to the menu.
   *
   * @param a_menu_mngr TODO
   */
  public final void contributeToMenu(final IMenuManager a_menu_mngr) {
    // Run super.
    super.contributeToMenu(a_menu_mngr);
    final MenuManager bytecodeMenu = new MenuManager("Editor"); //$NON-NLS-1$
    a_menu_mngr.insertAfter("additions", bytecodeMenu); //$NON-NLS-1$
    bytecodeMenu.add(my_action_plus);
    bytecodeMenu.add(my_action_minus);
    bytecodeMenu.add(my_refresh_action);
    bytecodeMenu.add(my_rebuild_action);
    bytecodeMenu.add(my_combine_action);
    bytecodeMenu.add(my_restore_action);
    bytecodeMenu.add(my_synchr_action);
  }

  /**
   * The current editor window is set as an attribute
   * (also for each action).
   *
   * @param an_editor  the current editor window
   */
  public final void setActiveEditor(final IEditorPart an_editor) {
    super.setActiveEditor(an_editor);
    my_bcode_cntrbtn.setActiveEditor(an_editor);
    my_action_plus.setActiveEditor(an_editor);
    my_action_minus.setActiveEditor(an_editor);
    my_refresh_action.setActiveEditor(an_editor);
    my_rebuild_action.setActiveEditor(an_editor);
    my_combine_action.setActiveEditor(an_editor);
    my_restore_action.setActiveEditor(an_editor);
    my_synchr_action.setActiveEditor(an_editor);
  }

  /**
   * The same as {@ref #refreshEditor(IEditorPart, IEditorInput)}, but
   * the input is obtained from the current editor window.
   *
   * @param an_editor TODO
   * @throws PartInitException if the new editor could not be created or
   *               initialized
   * @see #refreshEditor(BytecodeEditor, IEditorInput)
   */
  public final void refreshEditor(final BytecodeEditor an_editor)
    throws PartInitException {
    final IEditorInput input = an_editor.getEditorInput();
    refreshEditor(an_editor, input);
  }

  /**
   * Saves all settings of the current editor (selection positions,
   * contributions, JavaClass structure, related editor). Then closes the
   * editor and opens a new one with the same settings and given input.
   *
   * @param an_editor current editor to be closed
   * @param an_input input file to be displayed in new editor
   * @throws PartInitException if the new editor could not be created or
   *    initialized
   */
  public final void refreshEditor(final BytecodeEditor an_editor,
                                  final IEditorInput an_input)
    throws PartInitException {
    final IWorkbenchPage page = an_editor.getEditorSite().getPage();
    final ITextSelection selection = (ITextSelection)an_editor.
                                         getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final int len = selection.getLength();
    final CompilationUnitEditor related = ((BytecodeEditor)an_editor).
                                                           getRelatedEditor();
    final JavaClass jc = ((BytecodeEditor)an_editor).getJavaClass();
    final boolean proper = (related != null);
    my_bcode_cntrbtn.survive();
    if (proper) Composition.startDisas();
    page.closeEditor(an_editor, true);
    final IEditorPart newEditor = page.openEditor(an_input,
                        "umbra.BytecodeEditor", true);
    ((BytecodeEditor) newEditor).setRelation(related, jc);
    final ISelection ns = new TextSelection(off, len);
    final ISelectionProvider sp = ((AbstractTextEditor)newEditor).
                          getSelectionProvider();
    sp.setSelection(ns);
    my_bcode_cntrbtn.reinit();
    if (proper) Composition.stopDisas();
  }

  /**
   * This method disables the synchronisation action in the editor.
   */
  public final void synchrDisable() {
    my_synchr_action.setEnabled(false);
  }

  /**
   * This method enables the synchronisation action in the editor.
   */
  public final void synchrEnable() {
    my_synchr_action.setEnabled(true);
  }

  /**
   * debugging helper
   *
  /*private void controlPrint(JavaClass jc, int i) {
    Method meth = jc.getMethods()[i];
    UmbraPlugin.messagelog(meth.getCode().toString());
  }*/

  /**
   * @return the action to refresh the bytecode
   */
  public final BytecodeRefreshAction getRefreshAction() {
    return my_refresh_action;
  }
}
