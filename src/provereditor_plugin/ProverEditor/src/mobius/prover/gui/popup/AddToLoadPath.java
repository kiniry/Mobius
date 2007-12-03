package mobius.prover.gui.popup;


import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import mobius.prover.gui.jobs.ProverStatus;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.progress.UIJob;


/**
 * The action triggering a compilation deed.
 */
public class AddToLoadPath implements IActionDelegate {

	/** The current selection in the workbench */
	private IStructuredSelection fSel = null;
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	public void run(IAction action) {
		if(fSel == null)
			return;
		if(! (fSel.getFirstElement() instanceof IFolder))
			return;
		IFolder f = (IFolder) fSel.getFirstElement();
		
		String folder =  f.getProjectRelativePath().toString();
		String root =f.getProject().getLocation().toString();
		
		Job job = new AddingJob(f.getProject(), root, folder);
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
	    	if (o instanceof IFolder) {
	    		//IFolder f = (IFolder) o;
    			action.setEnabled(true);
    			return;
	    		
	    	}
		}
		action.setEnabled(false);
	}
	

	
	public class AddingJob extends Job {
		private String fRoot, fFolder;
		private IProject fProject;
		
		public AddingJob(IProject project, String root, String folder) {
			super("Adding path to ProverEditor paths...");
			fProject = project;
			fRoot = root;
			fFolder = folder;
		}

		protected IStatus run(IProgressMonitor monitor) {
			File f = new File(fRoot + File.separator + ".prover_paths");
			//System.out.println (f);
			try {
				Set<String> paths = getPaths(f); 
				paths.add(fFolder);
				writePaths(f, paths);
			}
			catch (IOException e) {
				return ProverStatus.getErrorStatus("Problem writing paths", e);
			}
			UIJob uij = new UIJob("Updating") {

				public IStatus runInUIThread(IProgressMonitor monitor) {
					try {
						fProject.refreshLocal(IResource.DEPTH_ONE, monitor);
					} catch (CoreException e) {
						// we don't care for errors
					}
					return ProverStatus.getOkStatus();
				}
				
			};
			uij.schedule();
			return ProverStatus.getOkStatus();
		}


		
	}
	public static Set<String> getPaths(String project) throws IOException {
		File f = new File(project + File.separator + ".prover_paths");
		return getPaths(f);
	}

	private static Set<String> getPaths(File f) throws IOException {
		Set<String> hs = new HashSet<String>();
		if(!f.exists())
			return hs;
		LineNumberReader lnr = new LineNumberReader(new FileReader(f));
		String s;
		while((s = lnr.readLine())!= null) {
			hs.add(s);
		}
		lnr.close();
		return hs;
	}

	private static void writePaths(File f, Set<String> paths) throws IOException {
		PrintStream ps = new PrintStream(new FileOutputStream(f));
		Iterator<String> iter = paths.iterator();
		while(iter.hasNext()) {
			ps.println(iter.next().toString());
		}
		ps.close();
	}	
	
}
