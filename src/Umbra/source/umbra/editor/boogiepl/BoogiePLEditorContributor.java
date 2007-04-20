/*
 * Created on 2005-05-03
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package umbra.editor.boogiepl;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;

import javax.swing.JOptionPane;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.Action;
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
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;
import org.eclipse.ui.texteditor.AbstractTextEditor;

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
	private BoogiePLEditorAction actionPlus;
	/**
	 * TODO
	 */
	private BoogiePLEditorAction actionMinus;
	/**
	 * TODO
	 */
	private BoogiePLRefreshAction refreshAction;
	/**
	 * TODO
	 */
	private BoogiePLRebuildAction rebuildAction;
	/**
	 * TODO
	 */
	private BoogiePLCombineAction combineAction;
	/**
	 * TODO
	 */
	private BoogiePLRestoreAction restoreAction;
	/**
	 * TODO
	 */
	private BoogiePLSynchrAction synchrAction;
	/**
	 * TODO
	 */
	private boolean needRefresh = false;
	/**
	 * TODO
	 */
	private int mod;
	
	/**
	 *	This class defines an action of changing coloring style. It is used
	 *  in two instances: one changes colors clockwise and the other counter-clockwise.  
	 */
	class BoogiePLEditorAction extends Action {
		/**
		 * TODO
		 */
		private Shell shell;
		/**
		 * TODO
		 */
		private IEditorPart activeEditor;
		/**
		 * TODO
		 */
		private int change;
		
		/**
		 * @param change	+1 for clockwise changing -1 otherwise.
		 */
		public BoogiePLEditorAction(int change) {
			super("Change color");
			this.change = change;
		}
		
		/**
		 * TODO
		 */
		public void setShell(Shell shell) {
			this.shell = shell;
		}
		
		/**
		 * This method changes global value related to the coloring style
		 * and refreshes the editor window. 
		 */
		public void run() {
			if (mod == IColorValues.models.length - 1) return;
			mod = (mod + change) % (IColorValues.models.length - 1);
			Composition.setMod(mod);
			if (activeEditor != null){
				try {
					needRefresh = true;
					refreshEditor(activeEditor);
				} catch (PartInitException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		
		/**
		 * TODO
		 */
		public void setActiveEditor(IEditorPart part) {
			activeEditor = part;
		}
	}
	
	
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
			synchrAction.setEnabled(true);
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
	public class BoogiePLRebuildAction extends Action {
		
		/**
		 * TODO
		 */
		private IEditorPart editor;
		
		/**
		 * TODO
		 */
		public void setActiveEditor(IEditorPart targetEditor) {
			editor = targetEditor;
		}
		
		/**
		 * TODO
		 */
		public BoogiePLRebuildAction() {
			super("Rebuild");
		}
		
		/**
		 * '_' file is chosen and rewritten into ordinary binary
		 * file. The modificated binaries are removed, input is
		 * updated and the editor window appropriately restored.
		 * 
		 */
		public void run() {
			IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
			IPath active = file.getFullPath();
			String fnameTo = active.toOSString().replaceFirst(".btc", ".class");
			String lastSegment = active.lastSegment().replaceFirst(".btc", ".class");
			String fnameFrom = active.removeLastSegments(1).append("_" + lastSegment).toOSString();
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot(); 
			IFile fileFrom = root.getFile(new Path(fnameFrom));
			IPath pathTo = new Path(fnameTo);
			IFile fileTo = root.getFile(pathTo);
			if (fileFrom.exists()) {
				try {
					fileTo.delete(true, null);
					fileFrom.copy(pathTo, true, null);
				} catch (CoreException e) {
					e.printStackTrace();
				}
			}
			try {
				((BoogiePLEditor)editor).refreshBoogiePL(active, null, null);
				IEditorInput input = new FileEditorInput(file);
				refreshEditor(editor, input);
			} catch (ClassNotFoundException e1) {
				e1.printStackTrace();
			} catch (CoreException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
			synchrAction.setEnabled(true);
		}
	}

	/**
	 * This class defines action that allows linking changes
	 * made to bytecode with these made to source Java code
	 * in case they are made to different methods.
	 * If modification happens in the same method, BoogiePL
	 * modification is privileged.
	 */
	class BoogiePLCombineAction extends Action {
		private Shell shell;
		private IEditorPart editor;
		
		public BoogiePLCombineAction() {
			super("Combine");
		}
		
		public void setShell(Shell shell) {
			this.shell = shell;
		}
		
		/**
		 * The action is similar to rebuild - it generates
		 * input from the original source in the same way.
		 * The difference is that after this all methods are
		 * checked for bytecode modifications and if one
		 * has been made, it is chosen and saved from JavaClass.
		 * 
		 * @see BoogiePLRebuildAction
		 */
		public void run() {
			JavaClass oldJc = ((BoogiePLEditor)editor).getJavaClass();
			//System.out.println("OLD JAVA CLASS:");
			//controlPrint(oldJc, 1);
			//controlPrint(oldJc, 2);
			IEditorPart related = ((BoogiePLEditor)editor).getRelatedEditor();
			if (related.isSaveOnCloseNeeded()) { 
				MessageDialog.openWarning(editor.getSite().getShell(), "BoogiePL", "You must save it before!");
				return;
			}	
			IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
			IPath path = file.getFullPath();
			String fnameFrom = path.toOSString().replaceFirst(".btc", ".class");
			String lastSegment = path.lastSegment().replaceFirst(".btc", ".class");
			String fnameTo = path.removeLastSegments(1).append("_" + lastSegment).toOSString();
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot(); 
			IFile fileFrom = root.getFile(new Path(fnameFrom));
			IPath pathTo = new Path(fnameTo);
			IFile fileTo = root.getFile(pathTo);
			try {
				fileTo.delete(true, null);
				fileFrom.copy(pathTo, true, null);
			} catch (CoreException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			String clname = path.removeFileExtension().lastSegment();
			String pathName = ((BoogiePLEditor)editor).getPath(path).toOSString();
			//System.out.println("WARNING: " + pathName + " D:\\smieci\\eclipse" + path.removeLastSegments(1).toOSString());
			ClassPath cp = new ClassPath(pathName);
			SyntheticRepository strin = SyntheticRepository.getInstance(cp);
			try {
				JavaClass jc = strin.loadClass(clname);
				//System.out.println("SOURCE JAVA CLASS:");
				//controlPrint(jc, 1);
				//controlPrint(jc, 2);
				strin.removeClass(jc);			
				ClassGen oldCg = new ClassGen(oldJc);
				ClassGen cg = new ClassGen(jc);
				int oldMeths = oldCg.getMethods().length;
				int meths = cg.getMethods().length;
				boolean[] modified = boogiePLContribution.getModified();
				for (int i = 0; i < modified.length && i < oldMeths && i < meths; i++) {
					if (modified[i]) cg.setMethodAt(oldCg.getMethodAt(i), i);
					System.out.println("" + i + (modified[i] ? " yes" : " no"));
				}
				jc = cg.getJavaClass();
				//System.out.println("NEW JAVA CLASS:");
				//controlPrint(jc, 1);
				//controlPrint(jc, 2);
				String fullName = ((BoogiePLEditor)editor).getPath(path).toOSString();
				jc.dump(fullName + "\\" + lastSegment);
				//System.out.println("WARNING: " + fullName + "\\" + lastSegment + " D:\\smieci\\eclipse" + fnameFrom);
				((BoogiePLEditor)editor).refreshBoogiePL(path, null, null);
				IEditorInput input = new FileEditorInput(file);
				refreshEditor(editor, input);
			} catch (ClassNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (CoreException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			synchrAction.setEnabled(true);
			
			
		}
		
		/**
		 * TODO
		 */
		public void setActiveEditor(IEditorPart part) {
			editor = part;
		}
	}
	
	/**
	 * This class defines action of restoring bytecode from
	 * history. Current verion is replaced with one of these
	 * kept in history as a file with bt1, bt2, etc. extension 
	 */
	class BoogiePLRestoreAction extends Action {
		/**
		 * TODO
		 */
		private Shell shell;
		/**
		 * TODO
		 */
		private IEditorPart editor;
		
		/**
		 * TODO
		 */
		public BoogiePLRestoreAction() {
			super("Restore");
		}
		
		/**
		 * TODO
		 */
		public void setShell(Shell shell) {
			this.shell = shell;
		}
		
		/**
		 * An input dialog to insert number of version is shown.
		 * Then the binary source file is replaced with the 
		 * appropriate historical version and new input is
		 * generated and put into the editor window.
		 */
		public void run() {		
			String strnum = JOptionPane.showInputDialog("Input version number (0 to 2):", "0");
			int num = 0;
			if (strnum == "1") num = 1;
			else if (strnum == "2") num = 2;
			String ext = ".bt" + num;
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot(); 
			IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
			IPath active = file.getFullPath();
			String fnameFrom = active.toOSString().replaceFirst(".btc", ext);
			IFile fileFrom = root.getFile(new Path(fnameFrom));
			if (!fileFrom.exists()) {
				MessageDialog.openInformation(shell, "Restore bytecode", "The file " + fnameFrom + " does not exist");
				return;
			}	
			try {
				file.delete(true, null);
				fileFrom.copy(active, true, null);
			} catch (CoreException e) {
				e.printStackTrace();
			}
			String lastSegment = active.lastSegment().replaceFirst(".btc", ".class");
			String clnameTo = active.removeLastSegments(1).append(lastSegment).toOSString();
			String clnameFrom = active.removeLastSegments(1).append("_" + num + "_" + lastSegment).toOSString();
			IFile classFrom = root.getFile(new Path(clnameFrom));
			IPath clpathTo = new Path(clnameTo);
			IFile classTo = root.getFile(clpathTo);
			try {
				classTo.delete(true, null);
				classFrom.copy(clpathTo, true, null);
			} catch (CoreException e) {
				e.printStackTrace();
			}
			try {
				((BoogiePLEditor)editor).refreshBoogiePL(active, null, null);
				IEditorInput input = new FileEditorInput(file);
				boolean[] modified = boogiePLContribution.getModified();
				boogiePLContribution.setModTable(modified);
				refreshEditor(editor, input);
			} catch (ClassNotFoundException e1) {
				e1.printStackTrace();
			} catch (CoreException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
			synchrAction.setEnabled(true);
		}
		
		public void setActiveEditor(IEditorPart part) {
			editor = part;
		}
	}

	/**
	 * This class defines action of synchronization bytecode
	 * position with appropriate point in source code.
	 *
	 * @see BoogiePLDocument
	 */
	class BoogiePLSynchrAction extends Action {
		
		/**
		 * TODO
		 */
		private AbstractTextEditor editor;
		
		/**
		 * TODO
		 */
		public BoogiePLSynchrAction() {
			super("Synchronize");
		}
		
		/**
		 * TODO
		 */
		public void setActiveEditor(IEditorPart targetEditor) {
			editor = (AbstractTextEditor)targetEditor;
		}

		/**
		 * TODO
		 */
		public void run() {
			ITextSelection selection = (ITextSelection)editor.getSelectionProvider().getSelection();
			int off = selection.getOffset();
			BoogiePLDocument bDoc = (BoogiePLDocument)editor.getDocumentProvider().getDocument(editor.getEditorInput());
			bDoc.synchronizeBS(off);
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
		actionPlus = new BoogiePLEditorAction(1);
		actionMinus = new BoogiePLEditorAction(IColorValues.models.length -2);
		refreshAction = new BoogiePLRefreshAction();
		rebuildAction = new BoogiePLRebuildAction();
		combineAction = new BoogiePLCombineAction();
		restoreAction = new BoogiePLRestoreAction();
		synchrAction = new BoogiePLSynchrAction();
		ImageDescriptor iconRight = ImageDescriptor.createFromURL(new URL(UmbraPlugin.getDefault().getDescriptor().getInstallURL(), "icons/chcol1.gif"));
		ImageDescriptor iconLeft = ImageDescriptor.createFromURL(new URL(UmbraPlugin.getDefault().getDescriptor().getInstallURL(), "icons/chcol2.gif"));
		ImageDescriptor refreshIcon = ImageDescriptor.createFromURL(new URL(UmbraPlugin.getDefault().getDescriptor().getInstallURL(), "icons/refresh.gif"));
		ImageDescriptor rebuildIcon = ImageDescriptor.createFromURL(new URL(UmbraPlugin.getDefault().getDescriptor().getInstallURL(), "icons/rebuild.gif"));
		ImageDescriptor combineIcon = ImageDescriptor.createFromURL(new URL(UmbraPlugin.getDefault().getDescriptor().getInstallURL(), "icons/combine.gif"));
		ImageDescriptor restoreIcon = ImageDescriptor.createFromURL(new URL(UmbraPlugin.getDefault().getDescriptor().getInstallURL(), "icons/restoreH.gif"));
		ImageDescriptor synchrIcon = ImageDescriptor.createFromURL(new URL(UmbraPlugin.getDefault().getDescriptor().getInstallURL(), "icons/synchr.gif"));
		actionPlus.setImageDescriptor(iconRight);
		actionMinus.setImageDescriptor(iconLeft);
		refreshAction.setImageDescriptor(refreshIcon);
		rebuildAction.setImageDescriptor(rebuildIcon);
		combineAction.setImageDescriptor(combineIcon);
		restoreAction.setImageDescriptor(restoreIcon);
		synchrAction.setImageDescriptor(synchrIcon);
		boogiePLContribution = BoogiePLContribution.newItem();
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
		toolBarManager.add(boogiePLContribution);
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
		actionPlus.setActiveEditor(editor);
		actionMinus.setActiveEditor(editor);
		refreshAction.setActiveEditor(editor);
		rebuildAction.setActiveEditor(editor);
		combineAction.setActiveEditor(editor);
		restoreAction.setActiveEditor(editor);
		synchrAction.setActiveEditor(editor);
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
	 * @param editor		current editor to be closed
	 * @param input			input file to be displayed in new editor
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
	public void synchrDisable() {
		synchrAction.setEnabled(false);
	}
	
	/**
	 * TODO
	 */
	private void controlPrint(JavaClass jc, int i) {
		Method meth = jc.getMethods()[i];
		System.out.println(meth.getCode().toString());
	}

}
