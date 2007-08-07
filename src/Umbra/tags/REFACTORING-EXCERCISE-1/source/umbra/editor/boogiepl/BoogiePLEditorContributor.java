/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.MalformedURLException;
import java.net.URL;

import org.apache.bcel.classfile.JavaClass;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorActionBarContributor;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import org.osgi.framework.Bundle;

import umbra.UmbraPlugin;
import umbra.editor.Composition;


/**
 * This is managing class that provides the editor with a set of properties,
 * color changing and checking syntax correctness.
 *
 * @author Samuel Willimann  (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLEditorContributor extends EditorActionBarContributor {

  /**
   * TODO.
   */
  private BoogiePLContribution my_boogiepl_cntrbtn;

  /**
   * TODO.
   */
  private BoogiePLVerifyAction my_verify_action;

  /* *
   * The current colouring style, see {@link ColorValues}.
   */
  //private int my_mode; it's never read

  /**
   * This is a class defining an action: save current bytecode
   * editor window and re-generate BoogiePL from BCEL structures.
   * This action is equal to generating bytecode again from the
   * Java code after saving binary file.
   */
  public class BoogiePLRefreshAction extends Action {
    /**
     * TODO.
     */
    private BoogiePLEditor my_editor;

    /**
     * TODO.
     */
    public BoogiePLRefreshAction() {
      super("Refresh");
    }

    /**
     * The current editor window is set as an attribute.
     *
     * @param a_target_editor the current editor window
     */
    public final void setActiveEditor(final IEditorPart a_target_editor) {
      my_editor = (BoogiePLEditor)a_target_editor;
    }

    /**
     * This method firstly saves the editor and then
     * creates new input from the JavaClass structure in BCEL.
     * Finally replaces content of the Editor window with
     * the newly generated input.
     */
    public final void run() {
      my_editor.doSave(null);
      final IPath active = ((FileEditorInput)my_editor.getEditorInput()).
                                                       getFile().getFullPath();
      final IFile file = ((FileEditorInput)my_editor.getEditorInput()).
                                                     getFile();
      try {
        final String[] commentTab = my_boogiepl_cntrbtn.getCommentTab();
        final String[] interlineTab = my_boogiepl_cntrbtn.getInterlineTab();
        for (int i = 0; i < interlineTab.length; i++) {
          UmbraPlugin.messagelog("" + i + ". " + interlineTab[i]);
        }
        ((BoogiePLEditor)my_editor).refreshBoogiePL(active, commentTab,
                                                 interlineTab);
        final FileEditorInput input = new FileEditorInput(file);
        final boolean[] modified = my_boogiepl_cntrbtn.getModified();
        my_boogiepl_cntrbtn.setModTable(modified);
        refreshEditor(my_editor, input);
      } catch (ClassNotFoundException e) {
        e.printStackTrace();
      } catch (CoreException e) {
        e.printStackTrace();
      }
    }
  }

  /**
   * This class defines action of restoring the previous version
   * of binary file (remembered with the name exteneded with '_')
   * and then generating bytecode directly from it.
   * All changes made to bytecode are cancelled then.
   * This action is equall to saving Java source file (such that
   * binary file are restored) and generating bytecode from this.
   */
  public class BoogiePLVerifyAction extends Action {

    /**
     * TODO.
     */
    public BoogiePLVerifyAction() {
      super("Verify");
    }

    /**
     * Currently, the method does nothing.
     *
     * @param a_target_editor the current editor window
     */
    public void setActiveEditor(final IEditorPart a_target_editor) {
    }

    /**
     * '_' file is chosen and rewritten into ordinary binary
     * file. The modificated binaries are removed, input is
     * updated and the editor window appropriately restored.
     *
     */
    public final void run() {
      // TODO Send BoogiePL code to Boogie
      String s = null;

      try {
        final Process p = Runtime.getRuntime().exec("Boogie test.bpl");

        final BufferedReader stdInput = new BufferedReader(
                                     new InputStreamReader(p.getInputStream()));
        final BufferedReader stdError = new BufferedReader(
                                     new InputStreamReader(p.getErrorStream()));

        // read the output from the command
        UmbraPlugin.messagelog("Here is the standard output of the command:\n");
        while ((s = stdInput.readLine()) != null) {
          UmbraPlugin.messagelog(s);
        }

        // read any errors from the attempted command
        UmbraPlugin.messagelog("Here is the standard error of the command " +
                               "(if any):\n");
        while ((s = stdError.readLine()) != null) {
          UmbraPlugin.messagelog(s);
        }

        System.exit(0);
      } catch (IOException e) {
        e.printStackTrace();
        // System.exit(-1);
      }
    }
  }

  /**
   * The constructor is executed when the editor is started.
   * It includes creating all actions and provide them with their icons.
   */
  public BoogiePLEditorContributor() {
    super();
    // my_mode = Composition.getMod(); it's never read
    my_verify_action = new BoogiePLVerifyAction();
    final ImageDescriptor a_verify_icon = getConvertIcon();
    my_verify_action.setImageDescriptor(a_verify_icon);
    my_boogiepl_cntrbtn = BoogiePLContribution.newItem();
    my_verify_action.setToolTipText("Verify with Boogie");
  }

  /**
   * This method creates the {@ref ImageDescriptor} for the icon for
   * conversion to BoogiePL.
   *
   * @return the image descriptor corresponding to the convert icon
   */
  private ImageDescriptor getConvertIcon() {
    final Bundle bundle = UmbraPlugin.getDefault().getBundle();
    final URL installURL = bundle.getEntry("/");
    ImageDescriptor a_verify_icon = null;
    try {
      a_verify_icon = ImageDescriptor.createFromURL(
                            new URL(installURL,
                                    "icons/convert_to_boogiepl.gif"));
    } catch (MalformedURLException e) {
      //This cannot happen.
      UmbraPlugin.messagelog("IMPOSSIBLE: createFromURL generated exception " +
                             "in BoogiePLEditorContributor()");
    }
    return a_verify_icon;
  }

  /**
   * New buttons for the actions are added to the toolbar.  We call the
   * superclass method and add:
   * <ul>
   *   <li>the widget of the BoogiePL contribution</li>
   *   <li>the verification action icon</li>
   * </ul>
   * @param a_tbar_mngr the toolbar into which the widgets are added
   * @see EditorActionBarContributor#contributeToToolBar(IToolBarManager)
   */
  public final void contributeToToolBar(final IToolBarManager a_tbar_mngr) {
    // Run super.
    super.contributeToToolBar(a_tbar_mngr);
    // Test status line.
    a_tbar_mngr.add(my_boogiepl_cntrbtn);
    a_tbar_mngr.add(my_verify_action);
  }

  /**
   * New items for the actions are added to the menu. This method
   * creates a menu with the title "Editor" and adds the menu
   * to <code>a_menu_manager</code>. It also adds a {@ref #my_verify_action}
   * to the "Editor" menu.
   *
   * @param a_menu_manager the menu menager to which we add components of the
   *                       current object
   * @see EditorActionBarContributor#contributeToMenu(IMenuManager)
   */
  public final void contributeToMenu(final IMenuManager a_menu_manager) {
    // Run super.
    super.contributeToMenu(a_menu_manager);
    final MenuManager bytecodeMenu = new MenuManager("Editor"); //$NON-NLS-1$
    a_menu_manager.insertAfter("additions", bytecodeMenu); //$NON-NLS-1$
    bytecodeMenu.add(my_verify_action);
  }

  /**
   * The current editor window is set as an attribute
   * (also for each action). TODO check
   *
   * @param an_editor  the current editor window
   */
  public final void setActiveEditor(final IEditorPart an_editor) {
    super.setActiveEditor(an_editor);
    if (an_editor instanceof BoogiePLEditor) {
      /*if (needRefresh ||
          !((BoogiePLEditor)my_editor).isUpdated()) try {
        refreshEditor(my_editor);
        needRefresh = false;
      } catch (PartInitException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }*/
      UmbraPlugin.messagelog("setActiveEditor in BoogiePLVerifyAction");
    }
    my_boogiepl_cntrbtn.setActiveEditor(an_editor);
    my_verify_action.setActiveEditor(an_editor);
    /*if (my_editor instanceof BoogiePLEditor) {
      ((BoogiePLEditor)my_editor).leave();
    }*/
  }

  /* * It's not used
   * The same as below with input obtained from the current editor window.
   * @param an_editor TODO
   * @throws PartInitException TODO
   * @see #refreshEditor(BoogiePLEditor, IEditorInput)
   */
  //private void refreshEditor(final BoogiePLEditor an_editor)
  //  throws PartInitException {
  //  final IEditorInput input = an_editor.getEditorInput();
  //  refreshEditor(an_editor, input);
  //}

  /**
   * Saves all settings of the current editor (selection positions,
   * contributions, JavaClass structure, related editor). Then closes the editor
   * and opens a new one with the same settings and given input.
   *
   * @param an_editor current editor to be closed
   * @param an_input input file to be displayed in new editor
   * @throws PartInitException if the new editor could not be created or
   *    initialized
   */
  private void refreshEditor(final BoogiePLEditor an_editor,
                             final IEditorInput an_input)
    throws PartInitException {

    final IWorkbenchPage page = an_editor.getEditorSite().getPage();
    final ITextSelection selection = (ITextSelection)an_editor.
                                          getSelectionProvider().getSelection();
    final int off = selection.getOffset();
    final int len = selection.getLength();
    final CompilationUnitEditor related = ((BoogiePLEditor)an_editor).
                                                             getRelatedEditor();
    final JavaClass jc = ((BoogiePLEditor)an_editor).getJavaClass();
    final boolean proper = (related != null);
    my_boogiepl_cntrbtn.survive();
    if (proper) Composition.startDisas();
    page.closeEditor(an_editor, true);
    final IEditorPart newEditor = page.openEditor(an_input,
                                                  "umbra.BoogiePLEditor", true);
    ((BoogiePLEditor) newEditor).setRelation(related, jc);
    final ISelection ns = new TextSelection(off, len);
    final ISelectionProvider sp = ((AbstractTextEditor)newEditor).
                                                         getSelectionProvider();
    sp.setSelection(ns);
    my_boogiepl_cntrbtn.reinit();
    if (proper) Composition.stopDisas();
  }

  /**
   * TODO
   */
  /*
  private void controlPrint(JavaClass jc, int i) {
    Method meth = jc.getMethods()[i];
    UmbraPlugin.messagelog(meth.getCode().toString());
  }*/
}
