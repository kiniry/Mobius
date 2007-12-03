package mobius.prover.gui.popup;

import java.io.IOException;

import mobius.prover.Prover;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;


/**
 * The action used to launch an external ide to edit the prover file.
 */
public class LaunchIde implements IActionDelegate {

	/** The current selection in the workbench */
	IStructuredSelection sel = null;

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	public void run(IAction action) {
		if(sel == null) return;
		Thread myJob = new Thread("Prover Ide") {
		      public void run() {
		    	  Object o = sel.getFirstElement();
		    	  if (o instanceof IFile) {
		    		  IFile f = (IFile) o;
		    		  String rawloc = f.getRawLocation().toString(); 
		    		  Prover prover = Prover.findProverFromFile(rawloc);
		    		  IPath parent = f.getParent().getRawLocation();
		    		  String [] path = null; 
		    		  if(parent != null) {
		    			  path = new String[2];
		    			  path[1] = parent.toString();
		    		  } else {
		    			  path = new String[1]; 
		    		  }
		    		  path[0] = f.getProject().getLocation().toString();
		    		  String [] cmds = prover.getTranslator().getIdeCommand(prover.getIde(), path,rawloc);
		    				  
		    			
		    		  try {
		    			  Process p = Runtime.getRuntime().exec(cmds);
		    					p.waitFor();
		    		  } catch (IOException e) {
		    			  System.err.println("I was unable to find an ide for TopLevel. Check the path.");
		    		  } catch (InterruptedException e2) {
		    			  e2.printStackTrace();
		    		  }
		    	  }
		      }
		   };
		   myJob.start();
		
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
	 */
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
}
