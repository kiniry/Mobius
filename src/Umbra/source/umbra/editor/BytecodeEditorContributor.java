/*
 * Created on 2005-05-03
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package umbra.editor;

import java.net.MalformedURLException;
import java.net.URL;

import org.apache.bcel.classfile.*;
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

import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;
import org.eclipse.ui.texteditor.AbstractTextEditor;

import umbra.UmbraPlugin;
import umbra.editor.actions.BytecodeCombineAction;
import umbra.editor.actions.BytecodeEditorAction;
import umbra.editor.actions.BytecodeRebuildAction;
import umbra.editor.actions.BytecodeRefreshAction;
import umbra.editor.actions.BytecodeRestoreAction;
import umbra.editor.actions.BytecodeSynchrAction;


/**
 * This is managing class that provides the editor with a set of
 * actions: rebuild, refresh, combine, restore from history,
 * synchronization of cursor's positions from Bytecode to Java code,
 * color changing and checking syntax correctness. 
 * 
 * @author Wojtek Wąs
 */
public class BytecodeEditorContributor extends EditorActionBarContributor {

	/**
	 * TODO
	 */
	private BytecodeContribution bytecodeContribution;
	/**
	 * The action to change the color mode to the next one.
	 */
	private BytecodeEditorAction actionPlus;
	/**
	 * The action to change the color mode to the previous one.
	 */
	private BytecodeEditorAction actionMinus;
	/**
	 * The action to refresh 
	 * TODO
	 */
	private BytecodeRefreshAction refreshAction;
	/**
	 * TODO
	 */
	private BytecodeRebuildAction rebuildAction;
	/**
	 * TODO
	 */
	private BytecodeCombineAction combineAction;
	/**
	 * TODO
	 */
	private BytecodeRestoreAction restoreAction;
	/**
	 * TODO
	 */
	private BytecodeSynchrAction synchrAction;
		
	/**
	 * The constructor is executed when the editor is started.
	 * It includes creating all actions and provide them with their icons.
	 * 
	 * @throws MalformedURLException
	 */
	public BytecodeEditorContributor() throws MalformedURLException {
		super();
		int mod = Composition.getMod();
		bytecodeContribution = BytecodeContribution.newItem();
		actionPlus = new BytecodeEditorAction(this, 1, mod);
		actionMinus = new BytecodeEditorAction(this, 
				                               IColorValues.models.length -2,
				                               mod);
		refreshAction = new BytecodeRefreshAction(this, bytecodeContribution);
		rebuildAction = new BytecodeRebuildAction(this);
		combineAction = new BytecodeCombineAction(this, bytecodeContribution);
		restoreAction = new BytecodeRestoreAction(this, bytecodeContribution);
		synchrAction = new BytecodeSynchrAction();
		URL installURL = UmbraPlugin.getDefault().getDescriptor().getInstallURL();
		ImageDescriptor iconRight = ImageDescriptor.createFromURL(new URL(installURL, "icons/change_color_backward.gif"));
		ImageDescriptor iconLeft = ImageDescriptor.createFromURL(new URL(installURL, "icons/change_color_forward.gif"));
		ImageDescriptor refreshIcon = ImageDescriptor.createFromURL(new URL(installURL, "icons/refresh.gif"));
		ImageDescriptor rebuildIcon = ImageDescriptor.createFromURL(new URL(installURL, "icons/rebuild.bytecode.gif"));
		ImageDescriptor combineIcon = ImageDescriptor.createFromURL(new URL(installURL, "icons/combine.gif"));
		ImageDescriptor restoreIcon = ImageDescriptor.createFromURL(new URL(installURL, "icons/restoreH.gif"));
		ImageDescriptor synchrIcon = ImageDescriptor.createFromURL(new URL(installURL, "icons/synchr.gif"));
		actionPlus.setImageDescriptor(iconRight);
		actionMinus.setImageDescriptor(iconLeft);
		refreshAction.setImageDescriptor(refreshIcon);
		rebuildAction.setImageDescriptor(rebuildIcon);
		combineAction.setImageDescriptor(combineIcon);
		restoreAction.setImageDescriptor(restoreIcon);
		synchrAction.setImageDescriptor(synchrIcon);
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
	public void contributeToToolBar(IToolBarManager toolBarManager) {
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
	 */
	public void contributeToMenu(IMenuManager menuManager) {
		// Run super.
		super.contributeToMenu(menuManager);
		MenuManager bytecodeMenu = new MenuManager("Editor"); //$NON-NLS-1$
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
	 * @param editor	the current editor window
	 */
	public void setActiveEditor(IEditorPart editor) {
		super.setActiveEditor(editor);
		if (editor instanceof BytecodeEditor) {
			/*if (needRefresh ||
					!((BytecodeEditor)editor).isUpdated()) try {
				refreshEditor(editor);
				needRefresh = false;
			} catch (PartInitException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}*/	
		}
		bytecodeContribution.setActiveEditor(editor);
		actionPlus.setActiveEditor(editor);
		actionMinus.setActiveEditor(editor);
		refreshAction.setActiveEditor(editor);
		rebuildAction.setActiveEditor(editor);
		combineAction.setActiveEditor(editor);
		restoreAction.setActiveEditor(editor);
		synchrAction.setActiveEditor(editor);
		/*if (editor instanceof BytecodeEditor) {
			((BytecodeEditor)editor).leave();
		}*/
	}
	
	/**
	 * The same as below with input obtained from the current editor window.
	 * 
	 * @see #refreshEditor(IEditorPart, IEditorInput)
	 */
	public void refreshEditor(IEditorPart editor) throws PartInitException {
		IEditorInput input = editor.getEditorInput();
		refreshEditor(editor, input);
	}
	
	/**
	 * Saves all settings of the current editor (selection positions, 
	 * contributions, JavaClass structure, related editor). Then closes the editor
	 * and opens a new one with the same settings and given input. 
	 * 
	 * @param editor		current editor to be closed
	 * @param input			input file to be displayed in new editor
	 * @throws PartInitException
	 */
	public void refreshEditor(IEditorPart editor, IEditorInput input) throws PartInitException {
		IWorkbenchPage page = editor.getEditorSite().getPage();
		ITextSelection selection = (ITextSelection)((AbstractTextEditor)editor).getSelectionProvider().getSelection();
		int off = selection.getOffset();
		int len = selection.getLength();
		AbstractDecoratedTextEditor related = ((BytecodeEditor)editor).getRelatedEditor();
		JavaClass jc = ((BytecodeEditor)editor).getJavaClass();
		boolean proper = (related != null);
		bytecodeContribution.survive();
		if (proper) Composition.startDisas();
		page.closeEditor(editor, true);
		IEditorPart newEditor = page.openEditor(input, "umbra.BytecodeEditor", true);
		((BytecodeEditor) newEditor).setRelation(related, jc);
		ISelection ns = new TextSelection(off, len);
		ISelectionProvider sp = ((AbstractTextEditor)newEditor).getSelectionProvider();
		sp.setSelection(ns);
		bytecodeContribution.reinit();
		if (proper) Composition.stopDisas();
	}
	
	/**
	 * TODO
	 */
	public void synchrDisable() {
		synchrAction.setEnabled(false);
	}

	/**
	 * TODO
	 */
	public void synchrEnable() {
		synchrAction.setEnabled(true);
	}
	/**
	 * TODO
	 */
	private void controlPrint(JavaClass jc, int i) {
		Method meth = jc.getMethods()[i];
		System.out.println(meth.getCode().toString());
	}

}
