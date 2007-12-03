/*
 * Created on Feb 18, 2005
 */
package mobius.prover.exec.toplevel.stream;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;

/**
 * This class is alike {@link java.io.PrintWriter} except that
 * the buffer is flushed after each print command.
 */
public class InputStreamHandler extends PrintWriter {
  
  /**
   * Construct a new InputStreamHandler for the stream o.
   * @param o The stream to write to.
   */
  public InputStreamHandler(OutputStream o) {
    super( new OutputStreamWriter(o));
  }

  /*
   *  (non-Javadoc)
   * @see java.io.PrintWriter#println(java.lang.String)
   */
  public void println(String str) {
    super.println(str);
    flush();
  }
  
  /*
   *  (non-Javadoc)
   * @see java.io.PrintWriter#print(java.lang.String)
   */
  public void print(String str) {
    super.print(str);
    flush();
  }
}
