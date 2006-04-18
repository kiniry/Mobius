package prover.exec.toplevel.stream;

/**
 * A listener to listen to 
 * {@link prover.exec.toplevel.stream.StreamHandler} events.
 * @author J. Charles
 */
public interface IStreamListener {
	/**
	 * Called when something is added to the stream.
	 * @param handler The handler originating the event
	 * @param str The string appened to the stream
	 */
	public void append(StreamHandler handler, String str);
}
