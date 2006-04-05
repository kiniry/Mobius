/*
 * Created on Feb 18, 2005
 *
 */
package prover.exec.toplevel.stream;

import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;

/**
 *
 *  @author jcharles
 */
public class ErrorStreamHandler implements Runnable{

	/**
	 * @param errorStream
	 */
	InputStream err = null;
	private boolean bStopEating = false;
	private boolean bStillEating = false;
	private LinkedList strPrompt = new LinkedList();
	private String strWarning = "";
	
	public ErrorStreamHandler(InputStream errorStream) {
		 err = errorStream;
	}
	public void run() {
		bStopEating = false;
		eat();
	}
	public void stopEating() {
		bStopEating = true;
	}
	
	public boolean isStillEating() {
		return bStillEating;
	}
	
	/*public void start() {
		
		bStopEating = false;
	}*/
	/**
	 * 
	 */
	public void eat() {
		int read = 0;
		bStopEating = false;
		bStillEating = true;
		try {
			StringBuffer str = new StringBuffer();
			while (!bStopEating) {
				if(err.available() >0) {	
					read = err.read();
					if(read != 249) {/* TopLevel Special char*/
						str.append((char)read);
					}
					else
						break;
				}
			}
			String[] lines = str.toString().split("\n");
			strWarning = "";
			for(int i = 0; i < lines.length -3; i++)
				strWarning += lines[i] + "\n";
			if(lines.length >1) strPrompt.addLast(lines[lines.length - 1]);
			//System.out.println("Coherence? "+strPrompt.getFirst());
		} catch (IOException e1) {
			//System.out.println(e1);
			//e1.printStackTrace();
		}
		bStillEating = false;
	}
	public boolean ready() throws IOException {
		return err.available() > 0;
	}
	
	public String getPrompt() {
		String str = (strPrompt.size()>0)?(String) strPrompt.removeFirst() : "";
		return  str;
	}
	public String getWarning() {
		return strWarning;
	}

	public String toString() {
		return "The last prompt wos " + getWarning() + getPrompt();
	}
}
