/*
 * Created on Feb 18, 2005
 */
package prover.exec.toplevel.stream;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.LinkedList;

/**
 *
 *  @author jcharles
 */
public class InputStreamHandler extends Thread{
	PrintWriter out = null;
	LinkedList list = new LinkedList();
	//private boolean bIsAlive;
	public InputStreamHandler(OutputStream o) {
		out = new PrintWriter( new OutputStreamWriter(o));
		//bIsAlive = true;
	}
	public void run() {
		try {
			while(true) {
				if(list.size() != 0) {
					out.println((String)list.removeFirst());
					out.flush();
				}

			}
		}
		catch (Exception e) {
			//bIsAlive = false;
		}
	}
	
	public void println(String str) {
		list.add(str);
		if(list.size() != 0) {
			out.println((String)list.removeFirst());
			out.flush();
		}
	}

}
