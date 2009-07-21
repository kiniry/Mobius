package mobius.cct.tools;

import java.io.InputStream;
import java.io.PrintStream;
import java.util.Locale;

/**
 * Environment in which a tool is run.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Environment {
  /**
   * Get input stream.
   * @return Input stream.
   */
  InputStream getInput();
  
  /**
   * Get output stream.
   * @return Output stream.
   */
  PrintStream getOutput();
  
  /**
   * Get error stream.
   * @return Error stream.
   */
  PrintStream getErr();
  
  /**
   * Command line arguments.
   * First argument is the name of this tool.
   * @return Array of arguments.
   */
  String[] getArgs();
  
  /**
   * Get locale.
   * @return Locale.
   */
  Locale getLocale();
}
