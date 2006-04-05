package prover.gui.popup;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;

import prover.Prover;
import prover.ProverEditorPlugin;

public class LaunchIde implements IActionDelegate {
	IStructuredSelection sel = null;
	public LaunchIde() {
		super();
	}
	
	public void run(IAction action) {
		if(sel == null) return;
		Thread myJob = new Thread("Prover Ide") {
		      public void run() {
		    	  Object o = sel.getFirstElement();
		    	  if (o instanceof IFile) {
		    		  IFile f = (IFile) o;
		    		  Prover prover = ProverEditorPlugin.getInstance().getProver("Coq");
		    		  String [] cmds = {
		    				  	prover.getIde(),
		    				  	f.getRawLocation().toString()
		    		  };
		    		  try {
		    				Process p = Runtime.getRuntime().exec(cmds);
		    				p.waitFor();
		    			} catch (IOException e) {
		    				System.err.println("I was unable to find an ide for Coq. Check the path.");
		    			} catch (InterruptedException e2) {
		    				e2.printStackTrace();
		    			}
		    	  }
		      }
		   };
		   myJob.start();
		
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
}
