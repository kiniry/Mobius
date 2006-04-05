package prover.exec.toplevel.stream;

import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.Iterator;

import prover.exec.IStreamListener;

public class StandardStreamHandler implements Runnable{
	private InputStream in;
	private StringBuffer buff = new StringBuffer();
	private StringBuffer internbuff = new StringBuffer();
	private boolean bHasFinished;
	public StandardStreamHandler(InputStream inputStream) {
		in = inputStream;
	}
	

	private HashSet hs = new HashSet();
	public void addStreamListener(IStreamListener isl) {
		hs.add(isl);
	}
	public void removeStreamListener(IStreamListener isl) {
		hs.remove(isl);
	}
	private void appendToListeners(String str){
		Iterator iter = hs.iterator();
		while(iter.hasNext()) {
			IStreamListener isl = (IStreamListener)iter.next();
			isl.append(str);
		}
	}
	
	public void fireToListeners() {
		this.appendToListeners(buff.toString());
	}
	public void read() throws IOException{
		int read = 1;
		// On mange differentes infos
		// int available = 0;
		char []cTab = new char [256];
		byte []bTab = new byte [256];
		while ((read  = in.available()) >= 0) {
			int toRead = (read %256);
			read = in.read(bTab, 0, (toRead == 0) ? 256 : toRead);
			if(in.available() == 0){
				bHasFinished = true;
			}
			else {
				bHasFinished = false;
			}
			for (int i = 0; i < cTab.length; i++) {
				cTab[i] = (char) bTab[i];
			}
			if(read > 0)
				internbuff.append(cTab,0, read);
			
			buff.append(internbuff);
			internbuff = new StringBuffer();
			//System.out.println("23: " + internbuff);
		}
	
	}
	
	public void clearBuffer() {
		fireToListeners();
		buff = new StringBuffer();
	}
	public String getBuffer() {
		return buff.toString();
	}
	
	public void run() {
		bHasFinished = false;
		try {
			read();
		} catch (IOException e) {
			//e.printStackTrace();
		}
		
		bHasFinished = true;	
	}
	
	public boolean hasFinished() {
		return bHasFinished;
	}
}
