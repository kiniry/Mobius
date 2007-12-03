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
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class LaunchIde implements IActionDelegate {

  /** The current selection in the workbench. */
  IStructuredSelection fSel;

   /** {@inheritDoc} */
  @Override
  public void run(final IAction action) {
    if (fSel == null) {
      return;
    }
    final Thread myJob = 
      new Thread("Prover Ide") {
        /** {@inheritDoc} */
        @Override
        public void run() {
          final Object o = fSel.getFirstElement();
          if (o instanceof IFile) {
            final IFile f = (IFile) o;
            final String rawloc = f.getRawLocation().toString(); 
            final Prover prover = Prover.findProverFromFile(rawloc);
            final IPath parent = f.getParent().getRawLocation();
            String [] path = null; 
            if (parent != null) {
              path = new String[2];
              path[1] = parent.toString();
            } 
            else {
              path = new String[1]; 
            }
            path[0] = f.getProject().getLocation().toString();
            final String [] cmds = prover.getTranslator().getIdeCommand(
                                            prover.getIde(), path, rawloc);
                
            
            try {
              final Process p = Runtime.getRuntime().exec(cmds);
              p.waitFor();
            } 
            catch (IOException e) {
              System.err.println("I was unable to find an ide for TopLevel. Check the path.");
            } 
            catch (InterruptedException e2) {
              e2.printStackTrace();
            }
          }
        }
      };
    myJob.start();
    
  }
  
  /** {@inheritDoc} */
  @Override
  public void selectionChanged(final IAction action, final ISelection selection) {
    if (selection instanceof IStructuredSelection) {
      fSel = (IStructuredSelection) selection;
      final Object o = fSel.getFirstElement();
      if (o instanceof IFile) {
        final IFile f = (IFile) o;
        if (f.toString().endsWith(".v")) {
          action.setEnabled(true);
          return;
        }
      }
    }
    action.setEnabled(false);
  }
}
