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

import prover.Prover;
import prover.gui.jobs.ProverStatus;

/**
 * The action triggering a compilation deed.
 */
public class CompileFile implements IActionDelegate {

	/** The current selection in the workbench */
	private IStructuredSelection fSel = null;
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	public void run(IAction action) {
		if(fSel == null)
			return;
		if(! (fSel.getFirstElement() instanceof IFile))
			return;
		IFile f = (IFile) fSel.getFirstElement();
		Prover prover = Prover.findProverFromFile(f.toString());
		if(prover == null)
			return;
		String name =  f.getLocation().toString();
		String [] path = {f.getProject().getLocation().toString(),
				f.getLocation().removeLastSegments(1).toString()
		};
		String[] cmd = prover.getTranslator().getCompilingCommand(prover.getCompiler().trim(), path, name);
		Job job = new CompilationJob(prover, f, cmd);
		job.schedule();
	}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		if (selection instanceof IStructuredSelection) {
			fSel = (IStructuredSelection) selection;
			Object o = fSel.getFirstElement();
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
	

	/**
	 * This class represents the Job used to compile a file.
	
	 */
	private static class CompilationJob extends Job {
		/** The file to compile */
		private IFile fFile;
		/** The command line to compile the file */
		private String [] fCmd;
		/** The current prover object assiciated with the current file */
		private Prover fProver;
		
		
		/**
		 * Create a new Compilation Job.
		 * @param prover the prover object to compile the file with
		 * @param file the file to compile
		 * @param cmd the command to compile the file
		 */
		public CompilationJob(Prover prover, IFile file, String[] cmd) {
			super("Compiling " + file.getName());
			fFile = file;
			fCmd = cmd;
			fProver = prover;
		}

		/*
		 *  (non-Javadoc)
		 * @see org.eclipse.core.internal.jobs.InternalJob#run(org.eclipse.core.runtime.IProgressMonitor)
		 */
		protected IStatus run(IProgressMonitor monitor) {
			try {
				System.out.println("here");
				Process p = Runtime.getRuntime().exec(fCmd);
				LineNumberReader in = new LineNumberReader( new InputStreamReader(p.getInputStream()));
				String s;
				String res = "";
				try {
					p.waitFor();
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				while((s = in.readLine()) != null){
					res += s + "\n";
//					System.out.println("1" + res);
					if (fProver.isErrorMsg(s)) {
						while((s = in.readLine()) != null)
							res += s + "\n";
						return ProverStatus.getErrorStatus("The fFile " + fFile.getName() + " was not compiled.", 
											res);  			
					}
					 			
				}in = new LineNumberReader( new InputStreamReader(p.getErrorStream()));
				while((s = in.readLine()) != null){
					res += s + "\n";
//					System.out.println("1" + res);
					if (fProver.isErrorMsg(s)) {
						while((s = in.readLine()) != null)
							res += s + "\n";
						return ProverStatus.getErrorStatus("The fFile " + fFile.getName() + " was not compiled.", 
											res);  			
					}
					 			
				}
				fFile.getParent().refreshLocal(IResource.DEPTH_ONE, monitor);
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
