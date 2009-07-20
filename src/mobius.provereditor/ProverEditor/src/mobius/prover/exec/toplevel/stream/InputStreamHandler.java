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
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class InputStreamHandler extends PrintWriter {
  
  /**
   * Construct a new InputStreamHandler for the stream o.
   * @param o The stream to write to.
   */
  public InputStreamHandler(final OutputStream o) {
    super(new OutputStreamWriter(o));
  }

  /** {@inheritDoc} */
  @Override
  public void println(final String str) {
    super.println(str);
    flush();
  }
  
  /** {@inheritDoc} */
  @Override
  public void print(final String str) {
    super.print(str);
    flush();
  }
}
