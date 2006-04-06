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
import prover.ProverEditorPlugin;
import prover.gui.jobs.ProverStatus;


public class CompileFile implements IActionDelegate {
	public void dispose() {

	}

	public void init(IWorkbenchWindow window) {

	}
	String[] cmdCoqC;
	private IStructuredSelection sel = null;
	public void run(IAction action) {
		if(sel == null)
			return;
		if(! (sel.getFirstElement() instanceof IFile))
			return;
		IFile f = (IFile) sel.getFirstElement();
		String name =  f.getLocation().toString();
		Prover p = ProverEditorPlugin.getInstance().getProver("Coq");
		String com = (p.getTop() + " -I " + f.getProject().getLocation() + 
				" -I " + f.getLocation().removeLastSegments(1) + 
				" -compile " + name.substring(0, name.length() -2)); 
		//System.out.println(com);
		cmdCoqC = com.replaceAll(" +", " ").split(" ");
		
		if(f.getName().endsWith(".v")) {
			Job job = new CompilationJob(f);
			job.schedule();
		}
	}

	public void selectionChanged(IAction action, ISelection selection) {
		if (selection instanceof IStructuredSelection) {
			sel = (IStructuredSelection) selection;
			Object o = sel.getFirstElement();
	    	if (o instanceof IFile) {
	    		IFile f = (IFile) o;
	    		if(f.toString().endsWith(".v")) {
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
				Process p = Runtime.getRuntime().exec(cmdCoqC);
				LineNumberReader in = new LineNumberReader( new InputStreamReader(p.getInputStream()));
				String s;
				String res = "";
				while((s = in.readLine()) != null){
					res += s + "\n";
					if (s.matches("Error.*")) {
						while((s = in.readLine()) != null)
							res += s + "\n";
						return ProverStatus.getErrorStatus("The file " + file.getName() + " was not compiled.", 
											res);  			
					}
					 			
				}
				file.getParent().refreshLocal(IResource.DEPTH_ONE, monitor);
			} catch (IOException e) {
				return ProverStatus.getErrorStatus(
						"I was unable to find the path to coqtop. Check the path." , 
							e.toString());
			} catch (CoreException e) {
				e.printStackTrace();
			} 		
			
			return ProverStatus.getOkStatus();
		}
	}
}
