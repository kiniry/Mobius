package mobius.prover.exec.toplevel.stream;

/**
 * A listener to listen to 
 * {@link mobius.prover.exec.toplevel.stream.StreamHandler} events.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IStreamListener {
  /**
   * Called when something is added to the stream.
   * @param handler The handler originating the event
   * @param str The string appened to the stream
   */
  void append(StreamHandler handler, String str);
}
