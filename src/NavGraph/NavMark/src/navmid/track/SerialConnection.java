package navmid.track;
import javax.comm.*;
import java.io.*;
import java.util.LinkedList;
import java.util.Queue;

/**
 * Handles the connection with the phone (or the emulator).
 * It is a low level driver that gives back a sequence of input lines.
 * @author piac6784
 *
 */
public class SerialConnection implements SerialPortEventListener, Runnable { 

	private InputStream	       is;
	private CommPortIdentifier portId;
	private SerialPort	       sPort = null;
	private String portName = ""; 
	private boolean	open;
	private final boolean modeSerial;
	private Queue <String> queue;
	private Thread t;
	private String socket;

	public SerialConnection(String s) {
		if (s == null) modeSerial = true;
		else { modeSerial = false; socket = s; }
		queue = new LinkedList<String>();
		open = false;
	}

	public void openConnection() {
		if (modeSerial) {
			// Obtain a CommPortIdentifier object for the port you want to open.
			try {
				portId = CommPortIdentifier.getPortIdentifier(portName);
				sPort = (SerialPort) portId.open("NavMark", 30000);
				is = sPort.getInputStream();
				sPort.addEventListener(this);
			} catch (Exception e) {
				if (sPort != null) sPort.close();
				System.err.println("Cannot set up connection: " + e.getMessage());
				return;
			} 

			// Event handling set-up. 30ms timeout before yielding back.
			sPort.notifyOnDataAvailable(true);
			sPort.notifyOnBreakInterrupt(true);
			try { sPort.enableReceiveTimeout(30); } 
			catch (UnsupportedCommOperationException e) {
				System.err.println("Unsupported operation (socat problem ?): " + e.getMessage());
			}
			open = true;
		} else { t = new Thread(this); t.start(); }
	} 

	public void closeConnection() {
		if (!open) return;
		if (modeSerial) {
			if (sPort != null) {
				try { is.close(); } 
				catch (IOException e) {	System.err.println(e); } 
				sPort.close();
				sPort = null;
			}
			open = false;
		} else {
			open = false;
			try { t.join(); } catch (InterruptedException e) { }
		}
	} 

	public boolean isOpen() { return open; } 

	public void serialEvent(SerialPortEvent e) {
		StringBuilder inputBuffer = new StringBuilder();
		int	newData = 0;

		switch (e.getEventType()) {
		case SerialPortEvent.DATA_AVAILABLE:
			while (newData != -1) {
				try {
					newData = is.read();
					if (newData == -1) break;
					if ((char) newData == '\n') {
						String line = inputBuffer.toString();
						synchronized(this) { System.err.println("Queueing"); queue.add(line); notify(); }
						inputBuffer = new StringBuilder();
					} else { inputBuffer.append((char) newData); } 
				} catch (IOException ex) { System.err.println(ex); break; } 
			} 
			break;
		case SerialPortEvent.BI:
			System.err.println("Break !");
		}
	} 

	public synchronized String get() {
		while(queue.isEmpty()) {
			try { wait(); } catch (InterruptedException e) { }
		}
		return queue.remove();
	} 

	public void run() {
		System.err.println("Inside loop started");
		open=true;
		FileInputStream is = null;
		try {
			is = new FileInputStream(socket);
			StringBuilder buf = new StringBuilder();
			while(open) {
				char c= (char) is.read();
				if ((c=='\n') || (c=='\r')) { 
					synchronized(this) {  
						queue.add(buf.toString()); 
						notify(); 
						buf = new StringBuilder(); }	
				}
				else buf.append(c);
			}
		} catch (IOException e) { 
			System.err.println("Connection problem: " + e);
			open = false;
		} finally {
			if (is != null) { try {is.close(); } catch (IOException e) { assert true; } }
		}
		System.err.println("Stopped");
	}
}
