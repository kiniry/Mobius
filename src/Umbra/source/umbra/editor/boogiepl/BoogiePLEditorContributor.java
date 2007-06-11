/*
 * Created on 2005-05-03
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
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
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import org.osgi.framework.Bundle;

import umbra.UmbraPlugin;
import umbra.editor.Composition;
import umbra.editor.IColorValues;


/**
 * This is managing class that provides the editor with a set of properties,
 * color changing and checking syntax correctness.
 *
 * @author Samuel Willimann
 */
public class BoogiePLEditorContributor extends EditorActionBarContributor {

  /**
   * TODO
   */
  private BoogiePLContribution boogiePLContribution;

  /**
   * TODO
   */
  private BoogiePLVerifyAction verifyAction;

  /**
   * The current colouring style, see {@link IColorValues}
   */
  private int mod;

  /**
   * This is a class defining an action: save current bytecode
   * editor window and re-generate BoogiePL from BCEL structures.
   * This action is equal to generating bytecode again from the
   * Java code after saving binary file.
   */
  public class BoogiePLRefreshAction extends Action {
    /**
     * TODO
     */
    private IEditorPart editor;

    /**
     * TODO
     */
    public BoogiePLRefreshAction() {
      super("Refresh");
    }

    /**
     * TODO
     */
    public void setActiveEditor(IEditorPart targetEditor) {
      editor = targetEditor;
    }

    /**
     * This method firstly saves the editor and then
     * creates new input from the JavaClass structure in BCEL.
     * Finally replaces content of the Editor window with
     * the newly generated input.
     */
    public void run() {
      editor.doSave(null);
      IPath active = ((FileEditorInput)editor.getEditorInput()).getFile().getFullPath();
      IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
      try {
        String[] commentTab = boogiePLContribution.getCommentTab();
        String[] interlineTab = boogiePLContribution.getInterlineTab();
        for (int i = 0; i < interlineTab.length; i++) {
          System.out.println("" + i + ". " + interlineTab[i]);
        }
        ((BoogiePLEditor)editor).refreshBoogiePL(active, commentTab, interlineTab);
        FileEditorInput input = new FileEditorInput(file);
        boolean[] modified = boogiePLContribution.getModified();
        boogiePLContribution.setModTable(modified);
        refreshEditor(editor, input);
      } catch (ClassNotFoundException e) {
        e.printStackTrace();
      } catch (CoreException e) {
        e.printStackTrace();
      } catch (IOException e) {
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
     * TODO
     */
    public void setActiveEditor(IEditorPart targetEditor) {
    }

    /**
     * TODO
     */
    public BoogiePLVerifyAction() {
      super("Verify");
    }

    /**
     * '_' file is chosen and rewritten into ordinary binary
     * file. The modificated binaries are removed, input is
     * updated and the editor window appropriately restored.
     *
     */
    public void run() {
      // TODO Send BoogiePL code to Boogie
      String s = null;

      try {
        Process p = Runtime.getRuntime().exec("Boogie test.bpl");

        BufferedReader stdInput = new BufferedReader(new InputStreamReader(p.getInputStream()));
        BufferedReader stdError = new BufferedReader(new InputStreamReader(p.getErrorStream()));

        // read the output from the command
        System.out.println("Here is the standard output of the command:\n");
        while ((s = stdInput.readLine()) != null) {
          System.out.println(s);
        }

        // read any errors from the attempted command
        System.out.println("Here is the standard error of the command (if any):\n");
        while ((s = stdError.readLine()) != null) {
          System.out.println(s);
        }

        System.exit(0);
      }
      catch (IOException e) {
        e.printStackTrace();
        // System.exit(-1);
      }
    }
  }

  /**
   * The constructor is executed when the editor is started.
   * It includes creating all actions and provide them with their icons.
   *
   * @throws MalformedURLException
   */
  public BoogiePLEditorContributor() throws MalformedURLException {
    super();
    mod = Composition.getMod();
    verifyAction = new BoogiePLVerifyAction();
    Bundle bundle = UmbraPlugin.getDefault().getBundle();
    URL installURL = bundle.getEntry("/");
    ImageDescriptor verifyIcon = ImageDescriptor.createFromURL(new URL(installURL, "icons/convert_to_boogiepl.gif"));
    verifyAction.setImageDescriptor(verifyIcon);
    boogiePLContribution = BoogiePLContribution.newItem();
    verifyAction.setToolTipText("Verify with Boogie");
  }

  /**
   * New buttons for the actions are added to the toolbar.
   */
  public void contributeToToolBar(IToolBarManager toolBarManager) {
    // Run super.
    super.contributeToToolBar(toolBarManager);
    // Test status line.
    toolBarManager.add(boogiePLContribution);
    toolBarManager.add(verifyAction);
  }

  /**
   * New items for the actions are added to the menu.
   */
  public void contributeToMenu(IMenuManager menuManager) {
    // Run super.
    super.contributeToMenu(menuManager);
    MenuManager bytecodeMenu = new MenuManager("Editor"); //$NON-NLS-1$
    menuManager.insertAfter("additions", bytecodeMenu); //$NON-NLS-1$
    bytecodeMenu.add(verifyAction);
  }

  /**
   * The current editor window is set as an attribute
   * (also for each action)
   *
   * @param editor  the current editor window
   */
  public void setActiveEditor(IEditorPart editor) {
    super.setActiveEditor(editor);
    if (editor instanceof BoogiePLEditor) {
      /*if (needRefresh ||
          !((BoogiePLEditor)editor).isUpdated()) try {
        refreshEditor(editor);
        needRefresh = false;
      } catch (PartInitException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }*/
    }
    boogiePLContribution.setActiveEditor(editor);
    verifyAction.setActiveEditor(editor);
    /*if (editor instanceof BoogiePLEditor) {
      ((BoogiePLEditor)editor).leave();
    }*/
  }

  /**
   * The same as below with input obtained from the current editor window.
   *
   * @see #refreshEditor(IEditorPart, IEditorInput)
   */
  private void refreshEditor(IEditorPart editor) throws PartInitException {
    IEditorInput input = editor.getEditorInput();
    refreshEditor(editor, input);
  }

  /**
   * Saves all settings of the current editor (selection positions,
   * contributions, JavaClass structure, related editor). Then closes the editor
   * and opens a new one with the same settings and given input.
   *
   * @param editor    current editor to be closed
   * @param input      input file to be displayed in new editor
   * @throws PartInitException
   */
  private void refreshEditor(IEditorPart editor, IEditorInput input) throws PartInitException {
    IWorkbenchPage page = editor.getEditorSite().getPage();
    ITextSelection selection = (ITextSelection)((AbstractTextEditor)editor).getSelectionProvider().getSelection();
    int off = selection.getOffset();
    int len = selection.getLength();
    AbstractDecoratedTextEditor related = ((BoogiePLEditor)editor).getRelatedEditor();
    JavaClass jc = ((BoogiePLEditor)editor).getJavaClass();
    boolean proper = (related != null);
    boogiePLContribution.survive();
    if (proper) Composition.startDisas();
    page.closeEditor(editor, true);
    IEditorPart newEditor = page.openEditor(input, "umbra.BoogiePLEditor", true);
    ((BoogiePLEditor) newEditor).setRelation(related, jc);
    ISelection ns = new TextSelection(off, len);
    ISelectionProvider sp = ((AbstractTextEditor)newEditor).getSelectionProvider();
    sp.setSelection(ns);
    boogiePLContribution.reinit();
    if (proper) Composition.stopDisas();
  }

  /**
   * TODO
   */
  /*
  private void controlPrint(JavaClass jc, int i) {
    Method meth = jc.getMethods()[i];
    System.out.println(meth.getCode().toString());
  }*/
}
