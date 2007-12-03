package mobius.prover.plugins;

import java.io.PrintStream;

/**
 * Logging utilities. 3 stream to write the different kind of messages.
 * The main feature is for the warning and error streams to have
 * the name of the file and the line written to the output.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Logger {
  /** the error stream. */
  public static final /*@ non_null @*/ NormalLogger err = new ErrorLogger();
  /** the warning stream. */
  public static final NormalLogger warn = new WarningLogger();
  /** the output stream. */
  public static final NormalLogger out = new NormalLogger();


  /**
   * A simple extension of a print stream for the standard
   * output.
   * It's the basis for the other logger classes.
   * @author J. Charles
   */
  public static class NormalLogger extends PrintStream {
    
    /**
     * Initialize the logger with the specified stream.
     * @param ps the stream to write to
     */
    protected NormalLogger(final PrintStream ps) {
      super(ps);
    }
    
    /**
     * Initialize the logger with {@link System#out}.
     */
    public NormalLogger() {
      this(System.out);
    }
    
    /**
     * Print the object class and then output the message
     * using the {@link #println(String)} method.
     * @param o the object from which its class has to be output
     * @param str the message
     */
    public void println(final Object o, final String str) {
      print(o.getClass());
      println(str);
    }
      
  }
  
  /**
   * When println is called the warning logger adds the
   * file and the line from where the logging message has
   * been generated. Otherwise it has the same behaviour as
   * {@link NormalLogger}.
   * @author J. Charles
   */
  public static class WarningLogger extends NormalLogger {
    /**
     * Initialize the logger with the specified stream.
     * @param ps the stream to write to
     */
    protected WarningLogger(final PrintStream ps) {
      super(ps);
    }
    
    /**
     * Initialize the logger with {@link System#out}.
     */
    public WarningLogger() {
    }

    /**
     * Print the parameter with the second element
     * of the stack trace (the file and the line where
     * this method was called) in front of it.
     * ie. it will give something like:
     * "Callee.java (233) : My message"
     * @param str the message to print
     */
    public void println(final String str) {
      final StackTraceElement [] ste = new Exception().getStackTrace();    
      super.println(ste[1] + ": " + str); 
    }
  }
  
  /**
   * It has the same behaviour as {@link WarningLogger} but it outputs
   * to the error stream.
   * @author J. Charles
   */
  public static final class ErrorLogger extends WarningLogger {
    /**
     * Initialize the logger with {@link System#err}.
     */
    public ErrorLogger() {
      super(System.err);
    }

  }

  

}
