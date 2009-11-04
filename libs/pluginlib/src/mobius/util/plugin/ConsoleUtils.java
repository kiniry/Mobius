package mobius.util.plugin;

import java.io.IOException;
import java.io.PrintStream;

import mobius.util.plugin.ImagesUtils.EImages;
import mobius.util.plugin.ImagesUtils.StreamConnection;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.console.IOConsoleOutputStream;



/**
 * All the utilities associated with the console that is used to output 
 * the result of the DirectVCGen.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class ConsoleUtils {
  /** the color red. */
  private static final RGB RED = new RGB(255, 0, 0);
  /** the color blue. */
  private static final RGB BLUE = new RGB(0, 0, 255);
  /** the color purple. */
  private static final RGB PURPLE = new RGB(255, 0, 255);
  /** the color black. */
  private static final RGB BLACK = new RGB(0, 0, 0);
  /** the current instance of console utils. */
  private static ConsoleUtils instance;

  /** the output console, used to write information to the user. */
  private IOConsole fConsole;
  /** the display dependent red color. */
  private Color fRed;
  /** the display dependent blue color. */
  private Color fBlue;
  /** the display dependent purple color. */
  private Color fPurple;
  /** the display dependent black color. */
  private Color fBlack;
  
  
  /**
   * The constructor, initialize all the datas.
   * @param name the name of the software eg. VCGen or whatever.
   */
  private ConsoleUtils(final String name) {
    instance = this;
    fConsole = new IOConsole("Mobius" + name + " Console", EImages.TOOL.getDescriptor());
    fConsole.activate();
    ConsolePlugin.getDefault().getConsoleManager().addConsoles(new IConsole[]{fConsole});
    final Display display = PlatformUI.getWorkbench().getDisplay();
    fRed = new Color(display, RED);
    fBlue = new Color(display, BLUE);
    fPurple = new Color(display, PURPLE);
    fBlack = new Color(display, BLACK);
  }
  
  /**
   * Returns the shared instance.
   *
   * @return the shared instance
   */
  public static ConsoleUtils getDefault() {
    if (instance == null) {
      instance = new ConsoleUtils("");
    }
    return instance;
  }
  
  /** {@inheritDoc} */
  protected void finalize() throws Throwable {
    fRed.dispose();
    fBlue.dispose();
    fPurple.dispose();
    fBlack.dispose();
    super.finalize();
  }
  /**
   * Returns the plugin console.
   * @return a valid console
   */
  public IOConsole getConsole() {
    return fConsole;
  }
  
  /**
   * Returns the color red.
   * @return not null
   */
  public Color getRed() {
    return fRed;
  }
  
  /**
   * Returns the color blue.
   * @return not null
   */
  public Color getBlue() {
    return fBlue;
  }
  
  /**
   * Returns the color black.
   * @return not null
   */
  public Color getBlack() {
    return fBlack;
  }
  /**
   * Returns the color purple.
   * @return not null
   */
  public Color getPurple() {
    return fPurple;
  }
  
  /**
   * Creates a job that does a system call, and outputs its result
   * in the standard console.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static class SystemCallJob extends Job {
    /** the arguments to run as the system call. */
    private final String[] fArgs;
  
    /**
     * Creates a SystemCallJob, a call to schedule has to be done
     * in order for the Job to run.
     * @param name the 'official' name for the job
     * @param args the commandline which has to be run
     */
    public SystemCallJob(final String name, final String [] args) {
      super(name);
      fArgs = args;
    }
  
    /** {@inheritDoc} */
    @Override
    protected IStatus run(final IProgressMonitor monitor) {
      final IOConsole console = ConsoleUtils.getDefault().getConsole();
      final IOConsoleOutputStream streamOut = console.newOutputStream();
      
      final IOConsoleOutputStream streamErr = console.newOutputStream();
      final IOConsoleOutputStream streamEnd = console.newOutputStream();
      streamErr.setColor(ConsoleUtils.getDefault().getRed());
      
      final PrintStream out = new PrintStream(streamEnd);
      streamEnd.setColor(ConsoleUtils.getDefault().getPurple());      
      
      try {
        final Process p = Runtime.getRuntime().exec(fArgs);
        final StreamConnection connexionOut = 
          new StreamConnection(p.getInputStream(), streamOut);
        final StreamConnection connexionErr = 
          new StreamConnection(p.getErrorStream(), streamErr);
        connexionOut.start();
        connexionErr.start();
        p.waitFor();
      } 
      catch (IOException e) {
        e.printStackTrace(out);
      } 
      catch (InterruptedException e) {
        e.printStackTrace(out);
      }
  
      out.println("\nDone!");
      return JobStatus.getOkStatus();      
    }
  }
  
  /**
   * Redirects the standard input and output to the current console.
   * Useful when a Java program is run in another Java program.
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static class ConsoleOutputWrapper {
    /** the current console where to write. */
    private final IOConsole fCurrent;
    /** the old output stream that will have to be restored. */
    private PrintStream fSavedOut;
    /** the old error stream that will have to be restored. */
    private PrintStream fSavedErr;
    
    /**
     * Initialize a new Console Wrapper.
     */
    public ConsoleOutputWrapper() {
      fCurrent = ConsoleUtils.getDefault().getConsole();
    }
    
    /**
     * Saves the current output and error stream if it hasn't been
     * done yet. If it has been already called once it does nothing.
     */
    public void wrap() {
      if (fSavedOut != null) {
        return;
      }
      fSavedOut = System.out;
      fSavedErr = System.err;
      final IOConsoleOutputStream out = fCurrent.newOutputStream();
      out.setColor(ConsoleUtils.getDefault().getBlack()); 
      
      System.setOut(new PrintStream(out));
      final IOConsoleOutputStream err = fCurrent.newOutputStream();
      err.setColor(ConsoleUtils.getDefault().getRed());      
      
      System.setErr(new PrintStream(err));
    }
    
    /**
     * Restores the standard output and error stream if they have been
     * previously saved. If {@link #wrap()} hasn't been called beforehand
     * it does nothing.
     */
    public void unwrap() {
      if (fSavedOut == null) {
        return;
      }
      System.setOut(fSavedOut);
      System.setErr(fSavedErr);
    }
  }
}
