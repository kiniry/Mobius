package bonIDE.diagram.custom;

import ie.ucd.bon.API;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import bonIDE.diagram.edit.parts.BONClassEditPart;
import bonIDE.diagram.edit.parts.ModelEditPart;

/**
 * Our sample action implements workbench action delegate.
 * The action proxy will be created by the workbench and
 * shown in the UI. When the user tries to use the action,
 * this delegate will be created and execution will be 
 * delegated to it.
 * @see IWorkbenchWindowActionDelegate
 */
public class StaticDiagramAction implements IWorkbenchWindowActionDelegate {
	
	private IWorkbenchWindow window;	
	private ModelEditPart modelEditPart;
	
	public StaticDiagramAction() {
	}

	
	/**
	 * The action has been activated. The argument of the method represents the 'real' action sitting
	 * in the workbench UI. @see IWorkbenchWindowActionDelegate#run
	 */
	public void run(IAction action) {
		
		FileDialog fd = new FileDialog(window.getShell(), SWT.OPEN);
		fd.setText("Open");
		fd.setFilterPath(
				"C:/Documents and Settings/ralph/My Documents/UCD/Thesis");
		String[] filterExt = { "*.bon", "*.*" };
		fd.setFilterExtensions(filterExt);
		String selected = fd.open();

		if( modelEditPart != null ){			
			BonDiagramElementBuilder.createBONStaticDiagram(selected, modelEditPart, window.getShell());			
		}		
	}

	/**
	 * Selection in the workbench has been changed. We 
	 * can change the state of the 'real' action here
	 * if we want, but this can only happen after 
	 * the delegate has been created.
	 * @see IWorkbenchWindowActionDelegate#selectionChanged
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		modelEditPart = null;
		if (selection instanceof IStructuredSelection) {
			IStructuredSelection structuredSelection = (IStructuredSelection) selection;
			if (structuredSelection.getFirstElement() instanceof ModelEditPart) {
				modelEditPart = (ModelEditPart) structuredSelection.getFirstElement();
			}
		}
	}

	/**
	 * We can use this method to dispose of any system
	 * resources we previously allocated.
	 * @see IWorkbenchWindowActionDelegate#dispose
	 */
	public void dispose() {
	}

	/**
	 * We will cache window object in order to
	 * be able to provide parent shell for the message dialog.
	 * @see IWorkbenchWindowActionDelegate#init
	 */
	public void init(IWorkbenchWindow window) {
		this.window = window;
	}
}