package prover.gui.popup;


import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IWorkbenchWindow;

import prover.Prover;
import prover.gui.jobs.ProverStatus;


public class CompileFile implements IActionDelegate {
	public void dispose() {

	}

	public void init(IWorkbenchWindow window) {

	}
	private Prover prover;
	String[] fCmd;
	private IStructuredSelection sel = null;
	public void run(IAction action) {
		if(sel == null)
			return;
		if(! (sel.getFirstElement() instanceof IFile))
			return;
		IFile f = (IFile) sel.getFirstElement();
		prover = Prover.findProverFromFile(f.toString());
		if(prover == null)
			return;
		String name =  f.getLocation().toString();
		String [] path = {f.getProject().getLocation().toString(),
				f.getLocation().removeLastSegments(1).toString()
		};
		fCmd = prover.getTranslator().getCompilingCommand(prover.getTop().trim(), path, name);
		Job job = new CompilationJob(f);
		job.schedule();
	}

	public void selectionChanged(IAction action, ISelection selection) {
		if (selection instanceof IStructuredSelection) {
			sel = (IStructuredSelection) selection;
			Object o = sel.getFirstElement();
	    	if (o instanceof IFile) {
	    		IFile f = (IFile) o;
	    		if(Prover.findProverFromFile(f.toString()) != null) {
	    			action.setEnabled(true);
	    			return;
	    		}
	    	}
		}
		action.setEnabled(false);
	}
	
	protected class CompilationJob extends Job {
		IFile file;
		String path;
		public CompilationJob(IFile f) {
			super("Compiling " + f.getName());
			file = f;
			path =  f.getRawLocation().toString();
		}

		protected IStatus run(IProgressMonitor monitor) {
			try {					
				Process p = Runtime.getRuntime().exec(fCmd);
				LineNumberReader in = new LineNumberReader( new InputStreamReader(p.getInputStream()));
				String s;
				String res = "";
				while((s = in.readLine()) != null){
					res += s + "\n";
					if (prover.isErrorMsg(s)) {
						while((s = in.readLine()) != null)
							res += s + "\n";
						return ProverStatus.getErrorStatus("The file " + file.getName() + " was not compiled.", 
											res);  			
					}
					 			
				}
				file.getParent().refreshLocal(IResource.DEPTH_ONE, monitor);
			} catch (IOException e) {
				return ProverStatus.getErrorStatus(
						"I was unable to find the path to the compilation program. Check the path." , 
							e.toString());
			} catch (CoreException e) {
				e.printStackTrace();
			} 		
			
			return ProverStatus.getOkStatus();
		}
	}
}
