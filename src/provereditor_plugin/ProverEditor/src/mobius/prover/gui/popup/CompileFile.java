package mobius.prover.gui.popup;


import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import mobius.prover.Prover;
import mobius.prover.gui.jobs.ProverStatus;

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


/**
 * The action triggering a compilation deed.
 */
public class CompileFile implements IActionDelegate {

  /** The current selection in the workbench. */
  private IStructuredSelection fSel;
  
  /** {@inheritDoc} */
  @Override
  public void run(final IAction action) {
    if (fSel == null) {
      return;
    }
    if (!(fSel.getFirstElement() instanceof IFile)) {
      return;
    }
    final IFile f = (IFile) fSel.getFirstElement();
    final Job job = compile(f, false);
    job.schedule();
  }

  /**
   * Compile the given file.
   * @param f the file to compile
   * @param silent if there has to be some prompt if the compilation fails
   * @return the created job or null
   */
  public static Job compile(final IFile f,  final boolean silent) {
    final Prover prover = Prover.findProverFromFile(f.toString());
    if (prover == null) {
      return null;
    }
    final String name =  f.getLocation().toString();
    Set<String> hsPath;
    try {
      hsPath = AddToLoadPath.getPaths(f.getProject().getLocation().toString());
    } 
    catch (IOException e) {
      hsPath = new HashSet<String>();
    }
    final String [] path = new String[hsPath.size() + 2];
    path [0] = f.getProject().getLocation().toString();
    path [1] = f.getLocation().removeLastSegments(1).toString();
    final Iterator<String> iter = hsPath.iterator();
    for (int i = 2; i < path.length; i++) {
      path[i] = path[0] + File.separator + iter.next().toString();
    }
    final String[] cmd = prover.getTranslator().getCompilingCommand(prover.getCompiler().trim(), 
                                                                    path, name);
    final Job job = new CompilationJob(prover, f, cmd, silent);
    return job;
  }

  /** {@inheritDoc} */
  @Override
  public void selectionChanged(final IAction action, 
                               final ISelection selection) {
    if (selection instanceof IStructuredSelection) {
      fSel = (IStructuredSelection) selection;
      final Object o = fSel.getFirstElement();
      if (o instanceof IFile) {
        final IFile f = (IFile) o;
        if (Prover.findProverFromFile(f.toString()) != null) {
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
    /** The file to compile. */
    private IFile fFile;
    /** The command line to compile the file. */
    private String [] fCmd;
    /** The current prover object assiciated with the current file. */
    private Prover fProver;
    /** tell if the job should be silent. */
    private boolean fIsSilent;
    
    /**
     * Create a new Compilation Job.
     * @param prover the prover object to compile the file with
     * @param file the file to compile
     * @param cmd the command to compile the file
     */
    public CompilationJob(final Prover prover, final IFile file, 
                          final String[] cmd, final boolean silent) {
      super("Compiling " + file.getName());
      fFile = file;
      fCmd = cmd;
      fProver = prover;
      fIsSilent = silent;
    }

    /** {@inheritDoc} */
    @Override
    protected IStatus run(final IProgressMonitor monitor) {
      try {
        //System.out.println("here");
        final Process p = Runtime.getRuntime().exec(fCmd);
        LineNumberReader in = new LineNumberReader(new InputStreamReader(p.getInputStream()));
        String s;
        String res = "";
        try {
          p.waitFor();
        } 
        catch (InterruptedException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        }
        while ((s = in.readLine()) != null) {
          res += s + "\n";
//          System.out.println("1" + res);
          if (fProver.isErrorMsg(s)) {
            while ((s = in.readLine()) != null) {
              res += s + "\n";
            }
            if (fIsSilent) {
              return ProverStatus.getOkStatus();
            }
            return ProverStatus.getErrorStatus(
                         "The file " + fFile.getName() + 
                         " was not compiled.", res);        
          }
                 
        }
        
        in = new LineNumberReader(new InputStreamReader(p.getErrorStream()));
        while ((s = in.readLine()) != null) {
          res += s + "\n";
//          System.out.println("1" + res);
          if (fProver.isErrorMsg(s)) {
            while ((s = in.readLine()) != null) {
              res += s + "\n";
            }
            
            if (fIsSilent) {
              return ProverStatus.getOkStatus();
            }
            return ProverStatus.getErrorStatus(
                             "The file " + fFile.getName() + 
                             " was not compiled.", res);        
          }
                 
        }
        fFile.getParent().refreshLocal(IResource.DEPTH_ONE, monitor);
      } 
      catch (IOException e) {
        if (fIsSilent) {
          return ProverStatus.getOkStatus();
        }
        return ProverStatus.getErrorStatus(
            "I was unable to find the path to the compilation program. Check the path." , 
              e.toString());
      } 
      catch (CoreException e) {
        e.printStackTrace();
      }     
      
      return ProverStatus.getOkStatus();
    }
  }
}
