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
import mobius.prover.plugins.AProverTranslator;
import mobius.prover.plugins.exceptions.ProverException;

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
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CompileFile implements IActionDelegate {

  /** The current selection in the workbench. */
  private IStructuredSelection fSel;
  
  /** {@inheritDoc} */
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
    final AProverTranslator trans = prover.getTranslator();
    final String[] cmd = trans.getCompilingCommand(prover.getCompiler().trim(), 
                                                                    path, name);
    final Job job = new CompilationJob(prover, f, cmd, silent);
    return job;
  }

  /** {@inheritDoc} */
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
    /** tell if the job should be silent, a silent job always terminates without error. */
    private boolean fIsSilent;
    
    /**
     * Create a new Compilation Job.
     * @param prover the prover object to compile the file with
     * @param file the file to compile
     * @param cmd the command to compile the file
     * @param silent set the verbosity of the compilation job
     */
    public CompilationJob(final Prover prover, final IFile file, 
                          final String[] cmd, final boolean silent) {
      super("Compiling " + file.getName());
      fFile = file;
      fCmd = cmd;
      fProver = prover;
      fIsSilent = silent;
    }

    /**
     * Parses the standard output from a given process.
     * @param p the process
     * @return the output
     * @throws ProverException if the prover returned an error message
     */
    private String parseStdOutput(final Process p) throws ProverException {
      final LineNumberReader in = 
        new LineNumberReader(new InputStreamReader(p.getInputStream()));
      // parse std output
      String res = "";
      String s;
      try {
        while ((s = in.readLine()) != null) {
          res += s + "\n";
  //        System.out.println("1" + res);
          if (fProver.isErrorMsg(s)) {
            while ((s = in.readLine()) != null) {
              res += s + "\n";
            }
            throw new ProverException(res);    
          }
                 
        }
      }
      catch (IOException e) {
        return null;
      }
      return res;
    }
    
    /**
     * Parses the error output from a given process.
     * @param p the process
     * @return the output
     * @throws ProverException if the prover returned an error message
     */
    private String parseErrOutput(final Process p) throws ProverException {
      // Parse errors
      final LineNumberReader in = 
        new LineNumberReader(new InputStreamReader(p.getErrorStream()));
      String res = "";
      String s;
      try {
        while ((s = in.readLine()) != null) {
          res += s + "\n";
  //        System.out.println("1" + res);
          if (fProver.isErrorMsg(s)) {
            while ((s = in.readLine()) != null) {
              res += s + "\n";
            }
  
            throw new ProverException(res); 
     
          }
        }
      }
      catch (IOException e) {
        return null;
      }
      return res; 
    }
    /** {@inheritDoc} */
    @Override
    protected IStatus run(final IProgressMonitor monitor) {
      try {
        final Process p = Runtime.getRuntime().exec(fCmd);
        try {
          p.waitFor();
        } 
        catch (InterruptedException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        }
        parseStdOutput(p);
        parseErrOutput(p);

        fFile.getParent().refreshLocal(IResource.DEPTH_ONE, monitor);
      } 
      catch (ProverException e) {
        if (!fIsSilent) {
          return ProverStatus.getErrorStatus(
                         "The file " + fFile.getName() + 
                         " was not compiled.", e.getMessage());
        }
      }
      catch (IOException e) {
        if (!fIsSilent) { 
          return ProverStatus.getErrorStatus(
            "I was unable to find the path to the compilation program. Check the path." , 
              e.toString());
        }
      } 
      catch (CoreException e) {
        e.printStackTrace();
      }     
      
      return ProverStatus.getOkStatus();
    }
  }
}
