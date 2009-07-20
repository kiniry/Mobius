//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: ProveFileAction.java
 /*
 /********************************************************************************
 /* Warnings/Remarks:
 /*******************************************************************************/
package jack.plugin.prove;

import jack.plugin.JackPlugin;
import jack.plugin.compile.CompileMessageDialog;
import jack.plugin.edit.SaveMessageDialog;
import jack.plugin.perspective.CaseExplorer;

import java.io.File;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import jpov.JpoFile;
import jpov.structure.Goal;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;

/**
 * Action allowing adding the selected file to the list of files that should be
 * proved.
 * 
 * @author A. Requet
 */
public abstract class ProveAction extends Action implements IObjectActionDelegate, Runnable {
	/** The current selection. */
	
	IStructuredSelection selection = null;
	private CaseExplorer caseExp = null;
//	private boolean bRun = false;
	/**
	 * @deprecated
	 * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(IAction,
	 *      IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		//activePart = targetPart;
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		run_proof(selection.iterator());
	}
	
	
	public void run() {
		
		Job myJob = new UIJob("ProofTask Job") {
		      public IStatus runInUIThread(IProgressMonitor monitor) {
		      	List g = caseExp.getEhl().getSelectedGoals();
				
					Iterator i = g.iterator();
					Goal a = null;
					while(i.hasNext()) {
						a = ((Goal)i.next()); 
						a.setSelected();
					}
					
					JpoFile j = caseExp.getJpoFile();
				
					IPath p = new Path(j.getDirectory() + File.separator + j.getJpoName());
					IFile f = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(p);
					run_proof_pec(f, j);
					//i = g.iterator();
//					bRun = false;
					
					return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
		      }
		   };
		   myJob.schedule();
			
	}
	public void run_proof_pec(IFile jpo_file, JpoFile j) {	
		IWorkbenchWindow win = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		IWorkbenchPage page = win.getActivePage();
		IWorkbenchPart part = page.getActivePart();
		//String r = ResourcesPlugin.getWorkspace().getRoot().getProject().getLocation().toString();
		IViewPart view;
		try {
			view = page.showView(JackPlugin.JACK_PROOF_VIEW_ID);
		} catch (PartInitException e) {
			MessageDialog.openError(win.getShell(), JackPlugin.DIALOG_TITLE,
					"Error showing view: " + e.toString());
			return;
		}
		
		if (!SaveMessageDialog.saveModifiedRessources(part, "proving",
				JackPlugin.ALWAYS_SAVE_BEFORE_PROVING))
			return;
		
		ProofView proof_view = (ProofView) view;
		List errors = null;
		proof_view.freezeNotify();

		if (jpo_file != null) {
			ProofTask p = getProofTask(jpo_file, null);
			p.setPartial(j.getDirectory().getAbsolutePath().toString());
			
			p.setJPov(j);
			p.setEndOp(caseExp.getEhl());
			p.setExplorer(caseExp);
			proof_view.addProof(p);
		}
	
		proof_view.unfreezeNotify();

		if (errors != null) {
			// 	errors have been encountered
			String message = "The following should be compiled before trying to prove them:";
			// adds the list of files
			Iterator files = errors.iterator();
			while (files.hasNext()) {
				message += "\n" + (String) files.next();
			}

			MessageDialog.openInformation(part.getSite().getShell(),
					JackPlugin.DIALOG_TITLE, message);
		}
	}
	
	public void run_proof(Iterator sel) {
			
		IWorkbenchWindow win = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		IWorkbenchPage page = win.getActivePage();
		IWorkbenchPart part = page.getActivePart();
		IViewPart view;
		try {
			view = page.showView(JackPlugin.JACK_PROOF_VIEW_ID);
		} catch (PartInitException e) {
			MessageDialog.openError(win.getShell(), JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}

		if (!SaveMessageDialog.saveModifiedRessources(part, "proving",
			JackPlugin.ALWAYS_SAVE_BEFORE_PROVING))
			return;

		ProofView proof_view = (ProofView) view;
		Iterator it = sel; //selection.iterator();

		List errors = null;
		proof_view.freezeNotify();
		while (it.hasNext()) {
			Object o = it.next();
			if (o instanceof ICompilationUnit) {
				ICompilationUnit c = (ICompilationUnit) o;

				if (JackPlugin.isLock(c.getResource())) {
					continue;
				}

				if (!CompileMessageDialog.compileRessources(c, part,
					"proving", 
					JackPlugin.ALWAYS_COMPILE_BEFORE_PROVING,
					getPropertyName()))
					break;

				IFile java_file = (IFile) c.getResource();
				IFile jpo_file = getJpoFile(c);

				if (jpo_file != null) {
					JackPlugin.lock(c.getResource());
					proof_view.addProof(getProofTask(jpo_file, c));
				} else {
					if (errors == null) {
						// creates the error vector if needed
						errors = new Vector();
					}
					// adds the file name
					errors.add(java_file.getName());
				}
			}
			else if (o instanceof IFile) {
				IFile jpo_file = (IFile) o;

				if (jpo_file != null) {
					//TODO Attention  null passe  la place du IFile
					proof_view.addProof(getProofTask(jpo_file, null));
				} else {
					if (errors == null) {
						// creates the error vector if needed
						errors = new Vector();
					}
					// adds the file name
					//errors.add(java_file.getName());
				}
			}
		}
		proof_view.unfreezeNotify();

		if (errors != null) {
			// errors have been encountered
			String message = "The following should be compiled before trying to prove them:";
			// adds the list of files
			Iterator files = errors.iterator();
			while (files.hasNext()) {
				message += "\n" + (String) files.next();
			}

			MessageDialog.openInformation(part.getSite().getShell(),
				JackPlugin.DIALOG_TITLE, message);
		}
	}

	/**
	 * Returns a ProofTask suitable for proving the given jpo file.
	 */
	protected abstract ProofTask getProofTask(IFile jpo_file, ICompilationUnit c);

	protected IFile getJpoFile(ICompilationUnit compilation_unit) {
		return JackPlugin.getJpoFile(compilation_unit);
	}
	
	protected QualifiedName getPropertyName() {
		return JackPlugin.JML_COMPILED;
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection sel) {
		IWorkbenchPart part = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActivePart();
		if (sel instanceof IStructuredSelection) {
			selection = (IStructuredSelection) sel;
		} else {
			// should never happen
			MessageDialog.openError(part.getSite().getShell(),
				"Jack Error",
				"Unexpected selection type: expected StructuredSelection, "
						+ "got " + sel.getClass().getName());
		}

	}

	/**
	 * @param explorer
	 */
	public void setCaseViewer(CaseExplorer explorer) {
		// TODO Auto-generated method stub
		caseExp = explorer;
	}


}