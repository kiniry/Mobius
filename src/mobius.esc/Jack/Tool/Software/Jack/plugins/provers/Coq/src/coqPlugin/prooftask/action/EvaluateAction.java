package coqPlugin.prooftask.action;

import jack.plugin.prove.CaseViewerUpdateJob;
import jack.util.Logger;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.progress.UIJob;

import coqPlugin.CoqFile;
import coqPlugin.ProverCoqStatus;
import coqPlugin.prooftask.util.CoqIdeThread;
import fr.inria.everest.coq.sugar.CoqUtils;

public class EvaluateAction implements IWorkbenchWindowActionDelegate {
	public void dispose() {

	}

	public void init(IWorkbenchWindow window) {

	}
	
	private FileEditorInput fei;
	private IEditorPart ed;
	public void run(IAction action) {
//		cmdCoqC = (CoqUtils.getCoqTop() + " -batch -l " + fei.getFile().getLocation()).replaceAll(" +", " ").split(" ");
		//Logger.get().println("ici");
		try {
			PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("CoqEditor.coqtopview");
		} catch (PartInitException e) {	}
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		ed = ap.getActiveEditor();
		String s = ed.getTitle();
		if(s.endsWith(".v")) {
			if (ed.getEditorInput() instanceof FileEditorInput) {	
				fei = (FileEditorInput)ed.getEditorInput();
				Job job = new Job("Evaluating " + fei.getName()) {
					String file;
					protected IStatus run(IProgressMonitor monitor) {
						if(ed.isDirty())
							return new Status(IStatus.ERROR, Platform.PI_RUNTIME, IStatus.OK, 
								"You must first save the file " + fei.getName() + " before evaluating it!" , null);

						try {
							
							file = fei.getPath().toString();
							if(CoqIdeThread.getGoal(file) == null)
								return new Status(IStatus.ERROR, Platform.PI_RUNTIME, IStatus.OK, 
										"The Coq file " + file + "was not linked to a goal in Jack's Coq plugin." , null);
							String ff = file.endsWith(".v") ? file.substring(0, file.length() -1) : file;
							String[] cmdCoqC  = CoqUtils.getCommand(null, ff);
							Process p = Runtime.getRuntime().exec(cmdCoqC);
							LineNumberReader in = new LineNumberReader( new InputStreamReader(p.getInputStream()));
							String s;
							boolean bWasProved = true;
							//in.wait();
							while((s = in.readLine()) != null){
								//Logger.get().println(s);
								if (s.matches("Error.*")) {
									bWasProved = false;
									return new Status(IStatus.ERROR, Platform.PI_RUNTIME, IStatus.OK, 
											"The goal from the file " + fei.getName() + " was not proved." , null);
								}
								
							}
							
							CoqIdeThread.getGoal(file).setStatus("Coq", new ProverCoqStatus(bWasProved, new CoqFile()));
							
							UIJob job = new UIJob ("Updating Case Viewer") {
								public IStatus runInUIThread(IProgressMonitor monitor) {
									Shell sh = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
									MessageDialog.openInformation(sh, "[Coq Plugin]: Evaluation of the vernacular file", "The goal contained in the file " + fei.getName() + " was proved succesfully.");
									UIJob job = new CaseViewerUpdateJob(CoqIdeThread.getExplorer(file));
									job.schedule();
									return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
								}
							};
							job.schedule();
							//CoqIdeThread.getInteractive(file).notifyResult(bWasProved);
						} catch (IOException e) {
							Logger.err.println("I was unable to find the path to coqtop. Check the path.");
						} 		
						return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
					}
					
				};
				
				job.schedule();
				//Logger.get().println(fei.getFile());
			}
		}
	}

	public void selectionChanged(IAction action, ISelection selection) {
		//try {
		//	PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("CoqEditor.coqtopview");
		//} catch (PartInitException e) {	}
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		if(ap.getActiveEditor()==null)
			return;
		IEditorInput ed = ap.getActiveEditor().getEditorInput();
		if(ed instanceof FileEditorInput) {
			FileEditorInput fei = (FileEditorInput) ed;
			this.fei = fei;
			action.setEnabled(CoqIdeThread.getGoal(fei.getPath().toString()) != null);
					
		}
		
	}

}
