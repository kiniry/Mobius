package mobius.directVCGen.ui.poview.util;

import java.io.IOException;
import java.io.PrintStream;

import mobius.directVCGen.ui.poview.util.ImagesUtils.StreamConnexion;

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

public class ConsoleUtils {
  /** the color red. */
  private static final RGB RED = new RGB(255, 0, 0);
  /** the color blue. */
  private static final RGB BLUE = new RGB(0, 0, 255);
  /** the color purple. */
  private static final RGB PURPLE = new RGB(255, 0, 255);
  /** the color black. */
  private static final RGB BLACK = new RGB(0, 0, 0);
  
  private static ConsoleUtils instance;

  /** the output console, used to write information to the user. */
  private IOConsole fConsole;
  /** the display dependent red color. */
  private Color fRed;
  /** the display dependent blue color. */
  private Color fBlue;
  /** the display dependent purple color. */
  private Color fPurple;
  private Color fBlack;
  
  
  private ConsoleUtils() {
    instance = this;
    fConsole = new IOConsole("Mobius DirectVCGen Console", ImagesUtils.descTool);
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
      instance = new ConsoleUtils();
    }
    return instance;
  }
  
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
  

  public static class SystemCallJob extends Job {
  
    private final String[] fArgs;
  
    public SystemCallJob(final String name, final String [] args) {
      super(name);
      fArgs = args;
    }
  
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
        final StreamConnexion connexionOut = 
          new StreamConnexion(p.getInputStream(), streamOut);
        final StreamConnexion connexionErr = 
          new StreamConnexion(p.getErrorStream(), streamErr);
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
  
  public static class ConsoleOutputWrapper {
    private final IOConsole fCurrent;
    private PrintStream savedOut;
    private PrintStream savedErr;
    
    /**
     * Initialize a new Console Wrapper.
     */
    public ConsoleOutputWrapper() {
      fCurrent = ConsoleUtils.getDefault().getConsole();
    }
    
    public void wrap() {
      if (savedOut != null) {
        return;
      }
      savedOut = System.out;
      savedErr = System.err;
      final IOConsoleOutputStream out = fCurrent.newOutputStream();
      out.setColor(ConsoleUtils.getDefault().getBlack()); 
      
      System.setOut(new PrintStream(out));
      final IOConsoleOutputStream err = fCurrent.newOutputStream();
      err.setColor(ConsoleUtils.getDefault().getRed());      
      
      System.setErr(new PrintStream(err));
    }
    
    public void unwrap() {
      if (savedOut == null) {
        return;
      }
      System.setOut(savedOut);
      System.setErr(savedErr);
    }
  }
}
