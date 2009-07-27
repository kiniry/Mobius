package mobius.cct.tools;

import java.io.InputStream;
import java.io.PrintStream;
import java.util.Locale;

/**
 * Default implementation of environment.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultEnvironment implements Environment {
  /**
   * Command line arguments.
   */
  private final String[] fArgs;
  
  /**
   * Locale.
   */
  private final Locale fLocale;
  
  /**
   * Constructor.
   * @param args Command line arguments.
   */
  public DefaultEnvironment(final String[] args) {
    final String lang = System.getProperty("user.lang");
    final String region = System.getProperty("user.region");
    if (lang == null) {
      fLocale = new Locale("en");
    } else {
      if (region == null) {
        fLocale = new Locale(lang);
      } else {
        fLocale = new Locale(lang, region);
      }
    }
    fArgs = args;
  }
  
  /**
   * Get arguments.
   * @return Arguments.
   */
  public String[] getArgs() {
    return fArgs;
  }

  /**
   * Get error stream.
   * @return System.err.
   */
  public PrintStream getErr() {
    return System.err;
  }


  /**
   * Get input stream.
   * @return System.in.
   */
  public InputStream getInput() {
    return System.in;
  }

  /**
   * Get output stream.
   * @return System.out.
   */
  public PrintStream getOutput() {
    return System.out;
  }

  /**
   * Get locale.
   * @return System locale.
   */
  public Locale getLocale() {
    return fLocale;
  }
  
}
