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

import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorActionBarContributor;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraPlugin;
import umbra.editor.actions.BytecodeColorAction;
import umbra.editor.actions.BytecodeCombineAction;
import umbra.editor.actions.BytecodeRebuildAction;
import umbra.editor.actions.BytecodeRefreshAction;
import umbra.editor.actions.BytecodeSynchrAction;
import umbra.editor.actions.history.BytecodeRestoreAction;
import umbra.editor.actions.history.ClearHistoryAction;
import umbra.editor.actions.history.HistoryAction;
import umbra.lib.EclipseIdentifiers;


/**
 * This is managing class that adds actions to workbench menus and toolbars
 * for a byte code editor. They appear when the editor is active. These actions
 * are in particular: rebuild, refresh, combine, restore from history,
 * synchronise the position of the cursor between the byte code and the Java
 * code, colour change and check of the syntax correctness.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeEditorContributor extends EditorActionBarContributor {

  /**
   * The identifier of the refresh action.
   */
  public static final String REFRESH_ID = "umbra.editor.Refresh";

  /**
   * TODO.
   */
  private BytecodeContribution my_bcode_cntrbtn;

  /**
   * The action to change the colour mode to the next one.
   */
  private BytecodeColorAction my_action_plus;

  /**
   * The action to change the colour mode to the previous one.
   */
  private BytecodeColorAction my_action_minus;

  /**
   * The action to refresh the content of the current byte code editor.
   */
  private BytecodeRefreshAction my_refresh_action;

  /**
   * TODO.
   */
  private BytecodeRebuildAction my_rebuild_action;

  /**
   * The action to combine the modifications from the source code editor
   * and from the byte code editor.
   */
  private BytecodeCombineAction my_combine_action;

  /**
   * The action to add one history snapshot.
   */
  private HistoryAction my_addhist_action;

  /**
   * The action to clear all the history snapshots that
   * were stored before.
   */
  private ClearHistoryAction my_clearhist_action;

  /**
   * The action to restore one of the history snapshots that
   * were stored before.
   */
  private BytecodeRestoreAction my_restore_action;

  /**
   * The action to synchronise the position in the byte code file with
   * the corresponding position in the source code file.
   */
  private BytecodeSynchrAction my_synchr_action;

  /**
   * The constructor is executed when the editor is started.
   * This action happens when there is no byte code editor pane in the
   * environment open and an action to open one is taken.
   * This constructor creates all actions and provides them with their icons
   * and tool tip texts. If necessary it assigns ids of the actions.
   */
  public BytecodeEditorContributor() {
    super();

    my_bcode_cntrbtn = BytecodeContribution.newItem();
    createActions();
    final URL installURL = UmbraPlugin.getDefault().getBundle().getEntry("/");
    assignIcons(installURL);
    setupToolTipTexts();
    my_refresh_action.setId(REFRESH_ID);
    setupColorActions(installURL, Composition.getMod());
  }

  /**
   * This method sets up the tool tip texts for all the actions except the
   * colour mode actions.
   */
  private void setupToolTipTexts() {
    my_refresh_action.setToolTipText("Refresh");
    my_rebuild_action.setToolTipText("Rebuild");
    my_combine_action.setToolTipText("Combine");
    my_addhist_action.setToolTipText("Add to history");
    my_clearhist_action.setToolTipText("Clear history");
    my_restore_action.setToolTipText("Restore");
    my_synchr_action.setToolTipText("Synchronize");
  }

  /**
   * This method creates the objects to handle all the actions except the
   * colour mode actions.
   */
  private void createActions() {
    my_refresh_action = new BytecodeRefreshAction(this, my_bcode_cntrbtn);
    my_rebuild_action = new BytecodeRebuildAction(this, my_bcode_cntrbtn);
    my_combine_action = new BytecodeCombineAction(this, my_bcode_cntrbtn);
    my_addhist_action = new HistoryAction(this, my_bcode_cntrbtn);
    my_clearhist_action = new ClearHistoryAction(this, my_bcode_cntrbtn);
    my_restore_action = new BytecodeRestoreAction(this, my_bcode_cntrbtn);
    my_synchr_action = new BytecodeSynchrAction(this, my_bcode_cntrbtn);
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
    my_action_plus = new BytecodeColorAction(this, my_bcode_cntrbtn, 1, a_mode);
    my_action_minus = new BytecodeColorAction(this, my_bcode_cntrbtn, -1,
                                              a_mode);
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
      ImageDescriptor addhist_icon;
      ImageDescriptor clearhist_icon;
      ImageDescriptor restore_icon;
      ImageDescriptor synchr_icon;
      refresh_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/refresh.gif"));
      rebuild_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/rebuild_bytecode.gif"));
      combine_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/combine.gif"));
      addhist_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/addH.gif"));
      clearhist_icon = ImageDescriptor.
      createFromURL(new URL(an_install_url, "icons/clearH.gif"));
      restore_icon = ImageDescriptor.
      createFromURL(new URL(an_install_url, "icons/restoreH.gif"));
      synchr_icon = ImageDescriptor.
        createFromURL(new URL(an_install_url, "icons/synchronize.gif"));
      my_refresh_action.setImageDescriptor(refresh_icon);
      my_rebuild_action.setImageDescriptor(rebuild_icon);
      my_combine_action.setImageDescriptor(combine_icon);
      my_addhist_action.setImageDescriptor(addhist_icon);
      my_clearhist_action.setImageDescriptor(clearhist_icon);
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
   *   <li>the refresh action icon</li>
   *   <li>the synchronisation icon</li>
   * </ul>
   * @param a_tbar_mngr the toolbar into which the widgets are added
   * @see EditorActionBarContributor#contributeToToolBar(IToolBarManager)
   */
  public final void contributeToToolBar(final IToolBarManager a_tbar_mngr) {
    // Run super.
    super.contributeToToolBar(a_tbar_mngr);
    a_tbar_mngr.add(my_refresh_action);
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
    final MenuManager bytecodeMenu =
      new MenuManager("Byte code", "umbra.bytecodeMenu"); //$NON-NLS-1$
    a_menu_mngr.insertAfter("additions", bytecodeMenu); //$NON-NLS-1$
    bytecodeMenu.add(my_refresh_action);
    bytecodeMenu.add(my_rebuild_action);
    bytecodeMenu.add(my_combine_action);
    bytecodeMenu.add(my_synchr_action);
    final Separator histGroup = new Separator("historyGroup");
    bytecodeMenu.add(histGroup);
    bytecodeMenu.appendToGroup("historyGroup", my_addhist_action);
    bytecodeMenu.appendToGroup("historyGroup", my_clearhist_action);
    bytecodeMenu.appendToGroup("historyGroup", my_restore_action);
    final Separator colourGroup = new Separator("colourGroup");
    bytecodeMenu.add(colourGroup);
    bytecodeMenu.appendToGroup("colourGroup", my_action_plus);
    bytecodeMenu.appendToGroup("colourGroup", my_action_minus);
    getActionBars().updateActionBars();
  }

  /**
   * The current editor window is set as an attribute
   * (also for each action).
   *
   * @param an_editor  the current editor window
   */
  public final void setActiveEditor(final IEditorPart an_editor) {
    final BytecodeEditor beditor = (BytecodeEditor) an_editor;
    super.setActiveEditor(an_editor);
    my_bcode_cntrbtn.setActiveEditor(an_editor);
    my_action_plus.setActiveEditor(an_editor);
    my_action_minus.setActiveEditor(an_editor);
    my_refresh_action.setActiveEditor(an_editor);
    beditor.setAction(REFRESH_ID, my_refresh_action);
    my_rebuild_action.setActiveEditor(an_editor);
    my_combine_action.setActiveEditor(an_editor);
    my_addhist_action.setActiveEditor(an_editor);
    my_clearhist_action.setActiveEditor(an_editor);
    my_restore_action.setActiveEditor(an_editor);
    my_synchr_action.setActiveEditor(an_editor);
  }

  /**
   * The same as
   * {@link #refreshEditor(BytecodeEditor, IEditorInput, String[], String[])},
   * but the input is obtained from the current editor window.
   *
   * @param an_editor TODO
   * @param the_interline an array with multi-line comments
   * @param the_comments an array with end-of-line comments
   * @throws PartInitException if the new editor could not be created or
   *   initialised
   * @see #refreshEditor(BytecodeEditor, IEditorInput, String[], String[])
   */
  public final BytecodeEditor refreshEditor(final BytecodeEditor an_editor,
                                  final String[] the_comments,
                                  final String[] the_interline)
    throws PartInitException {
    final IEditorInput input = an_editor.getEditorInput();
    return refreshEditor(an_editor, input, the_comments, the_interline);
  }

  /**
   * Saves all settings of the current editor (selection positions,
   * contributions, JavaClass structure, related editor). Then closes the
   * editor and opens a new one with the same settings and given input.
   *
   * @param an_editor current editor to be closed
   * @param an_input input file to be displayed in new editor
   * @param a_comment_array contains the texts of end-of-line comments, the
   *   i-th entry contains the comment for the i-th instruction in the file,
   *   if this parameter is null then the array is not taken into account
   * @param an_interline multi-line comments TODO fix the protocol
   * @return the new editor
   * @throws PartInitException if the new editor could not be created or
   *    initialised
   */
  public final BytecodeEditor refreshEditor(final BytecodeEditor an_editor,
                                  final IEditorInput an_input,
                                  final String[] a_comment_array,
                                  final String[] an_interline)
    throws PartInitException {
    final IWorkbenchPage page = an_editor.getEditorSite().getPage();
    final CompilationUnitEditor related = ((BytecodeEditor)an_editor).
                                                           getRelatedEditor();
    final boolean proper = (related != null);
    my_bcode_cntrbtn.survive();
    if (proper) Composition.startDisas();
    //TODO consider not closing the editor here
    page.closeEditor(an_editor, true);
    final BytecodeEditor newEditor = (BytecodeEditor)(page.openEditor(an_input,
                        EclipseIdentifiers.BYTECODE_EDITOR_CLASS, true));
    final BytecodeDocument ndoc = (BytecodeDocument)newEditor.
                                            getDocumentProvider().
                                            getDocument(an_input);
    //XXX changed: copying bmlp from old to the new copy of byte code editor.
    final BMLParsing bmlp = ((BytecodeEditor)an_editor).getDocument().getBmlp();
    ndoc.setEditor((BytecodeEditor)newEditor, bmlp);
    ndoc.reinit(a_comment_array, an_interline);
    ((BytecodeEditor) newEditor).setRelation(related);
    if (proper) Composition.stopDisas();
    return newEditor;
  }

  /**
   * debugging helper
   *
  /*private void controlPrint(JavaClass jc, int i) {
    Method meth = jc.getMethods()[i];
    UmbraPlugin.messagelog(meth.getCode().toString());
  }*/

  /**
   * @return the action to refresh the byte code
   */
  public final BytecodeRefreshAction getRefreshAction() {
    return my_refresh_action;
  }
}
