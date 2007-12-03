package mobius.prover.exec.toplevel.stream;

import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.Set;

/**
 * A stream handler is used to manage a stream.
 * It associates a stream with a thread in order to read
 * it asynchonously, in a non-blocking way.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class StreamHandler implements Runnable {
  /** the size of the buffer used to read the stream. */
  private static final int SIZE = 256;
  /** the input stream from which we read the input. */
  private InputStream fIn;
  /** the buffer to which input is added. */
  private StringBuffer fBuff = new StringBuffer();
  /** tells if input is still being read. */
  private boolean fHasFinished;
  /** the current thread. */ 
  private Thread fThread;
  /** the list of listeners. */
  private Set<IStreamListener> fListenerSet = new HashSet<IStreamListener>();
  
  /**
   * Create a new Stream Handler for the specified stream.
   * @param inputStream The input stream to create a handler for
   */
  protected StreamHandler(final InputStream inputStream) {
    fIn = inputStream;
  }

  /**
   * Sets the thread associated with the handler.
   * @param t the new thread to associate with the handler
   */
  protected void setThread(final Thread t) {
    fThread = t;
  }
  
  /**
   * Returns the current thread associated with the hamdler.
   * @return a valid thread or null if it has not been set yet 
   */
  public Thread getThread() {
    return fThread;
  }
  
  /**
   * Creates a new Stream Handler with a new thread to read infos from a stream.
   * It then starts the thread.
   * @param inputStream the sourced stream
   * @return The new stream handler object
   */
  public static StreamHandler createStreamHandler(final InputStream inputStream) {
    final StreamHandler sh = new StreamHandler(inputStream);
    final Thread t = new Thread(sh);
    t.start();
    sh.setThread(t);
    return sh;
  }
  
  /**
   * Add a listener to listen to the events of this thread.
   * @param isl the listener to add
   */
  public void addStreamListener(final IStreamListener isl) {
    fListenerSet.add(isl);
  }
  
  /**
   * Remove a listener that was previously registered to the stream.
   * @param isl the listener to remove
   */
  public void removeStreamListener(final IStreamListener isl) {
    fListenerSet.remove(isl);
  }
  
  /**
   * Sends to the listeners the event that text has been added to the
   * stream.
   */
  protected void fireToListeners() {
    final String str = fBuff.toString();
    for (IStreamListener isl: fListenerSet) {
      isl.append(this, str);
    }
  }

  
  /**
   * Read from the stream until there is an error.
   * the method never returns. It fills the buffer
   * with the stream content.
   * @throws IOException If there was an error from the stream
   */
  protected void read() throws IOException {
    int read = 1;
    StringBuffer buff = new StringBuffer();
    // On mange differentes infos
    final char [] cTab = new char [SIZE];
    final byte [] bTab = new byte [SIZE];
    while ((read  = fIn.available()) >= 0) {
      final int toRead = (read % SIZE);
      read = fIn.read(bTab, 0, (toRead == 0) ? SIZE : toRead);
      if (fIn.available() == 0) {
        fHasFinished = true;
      }
      else {
        fHasFinished = false;
      }
      for (int i = 0; i < cTab.length; i++) {
        cTab[i] = (char) bTab[i];
      }
      if (read > 0) {
        buff.append(cTab, 0, read);
      }
      
      fBuff.append(buff);
      buff = new StringBuffer();
    }
  
  }
  
  
  /**
   * Empty the buffer.
   */
  public void clearBuffer() {
    fireToListeners();
    fBuff = new StringBuffer();
  }
  
  /**
   * Return the current String which was just read by the
   * stream.
   * @return a copy of the internal buffer
   */
  public String getBuffer() {
    return fBuff.toString();
  }
  
  
  /** {@inheritDoc} */
  @Override
  public void run() {
    fHasFinished = false;
    try {
      read();
    } 
    catch (IOException e) {
      e.printStackTrace();
    }
    
    fHasFinished = true;  
  }
  
  /**
   * If no input is available anymore it is considered to be finished.
   * @return tells if there is no more input available
   */
  public boolean hasFinished() {
    return fHasFinished;
  }
}
