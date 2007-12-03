package mobius.prover.exec.toplevel.stream;

import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.Iterator;

/**
 * A stream handler is used to manage a stream.
 * It associates a stream with a thread in order to read
 * it asynchonously, in a non-blocking way.
 */
public class StreamHandler implements Runnable{
	/** the input stream from which we read the input */
	private InputStream fIn;
	/** the buffer to which input is added */
	private StringBuffer fBuff = new StringBuffer();
	/** tells if input is still being read */
	private boolean fbHasFinished;
	/** the current thread */ 
	private Thread fThread;
	/** the list of listeners */
	private HashSet fListenerSet = new HashSet();
	
	/**
	 * Create a new Stream Handler for the specified stream
	 * @param inputStream The input stream to create a handler for
	 */
	protected StreamHandler(InputStream inputStream) {
		fIn = inputStream;
	}

	/**
	 * Sets the thread associated with the handler.
	 * @param t the new thread to associate with the handler
	 */
	protected void setThread(Thread t) {
		fThread = t;
	}
	
	/**
	 * Returns the current thread associated with the hamdler
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
	public static StreamHandler createStreamHandler(InputStream inputStream) {
		StreamHandler sh = new StreamHandler(inputStream);
		Thread t = new Thread(sh);
		t.start();
		sh.setThread(t);
		return sh;
	}
	
	/**
	 * Add a listener to listen to the events of this thread.
	 * @param isl the listener to add
	 */
	public void addStreamListener(IStreamListener isl) {
		fListenerSet.add(isl);
	}
	
	/**
	 * Remove a listener that was previously registered to the stream
	 * @param isl the listener to remove
	 */
	public void removeStreamListener(IStreamListener isl) {
		fListenerSet.remove(isl);
	}
	
	/**
	 * Sends to the listeners the event that text has been added to the
	 * stream.
	 */
	protected void fireToListeners() {
		String str = fBuff.toString();
		Iterator iter = fListenerSet.iterator();
		while(iter.hasNext()) {
			IStreamListener isl = (IStreamListener)iter.next();
			isl.append(this, str);
		}
	}

	
	/**
	 * Read from the stream until there is an error.
	 * the method never returns. It fills the buffer
	 * with the stream content.
	 * @throws IOException If there was an error from the stream
	 */
	protected void read() throws IOException{
		int read = 1;
		StringBuffer buff = new StringBuffer();
		// On mange differentes infos
		char []cTab = new char [256];
		byte []bTab = new byte [256];
		while ((read  = fIn.available()) >= 0) {
			int toRead = (read %256);
			read = fIn.read(bTab, 0, (toRead == 0) ? 256 : toRead);
			if(fIn.available() == 0){
				fbHasFinished = true;
			}
			else {
				fbHasFinished = false;
			}
			for (int i = 0; i < cTab.length; i++) {
				cTab[i] = (char) bTab[i];
			}
			if(read > 0)
				buff.append(cTab,0, read);
			
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
	
	
	
	/*
	 *  (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		fbHasFinished = false;
		try {
			read();
		} catch (IOException e) {}
		
		fbHasFinished = true;	
	}
	
	/**
	 * If no input is available anymore it is considered to be finished.
	 * @return tells if there is no more input available
	 */
	public boolean hasFinished() {
		return fbHasFinished;
	}
}
