package navmark;
import java.util.*;
import java.io.*;
import javax.microedition.io.*;


/**
 * Sends back the events to the desktop. We use the serial communication usually well implemented 
 * on devices even if it is through serial usb and not with infrared or a real serial line.
 * Sun device emulator also implements it but is is more of a non configurable hack and it is 
 * hard to capture (requires socat). 
 * 
 * @author piac6784
 *
 */
class CommPrinter implements Runnable {

	private static final String protocol = "comm:";
	private static CommPrinter instance;

	private byte [] contents;
	
	private OutputStream  os;
	private CommConnection co;
	private String address;
	private Vector stack = new Vector();

	public CommPrinter() { 
		instance = this;
		String ports = System.getProperty("microedition.commports");
		// Takes the first port only.
		int comma_pos = ports.indexOf(',');
		if (comma_pos > 0) ports = ports.substring(0,comma_pos); 
		address = protocol + ports;
	}
	
	public void run() {
		try {
			co = (CommConnection) Connector.open(address);
			os = co.openOutputStream();
			while(true) {
				synchronized(this) {
					while(stack.size() == 0) {
						try { wait(); } catch (InterruptedException e) {}; 
					}
					contents = ((String) stack.elementAt(0)).getBytes();
					stack.removeElementAt (0);
				}
				os.write(contents);
				os.flush();
			}
		} catch (IOException e) { e.printStackTrace(); }
	}

	private synchronized void write(String msg) {
		// Only visible on the console. Useful in emulator not on a phone.
		System.err.print(msg);
		stack.addElement (msg);
		notify(); 
	}

	static void print(String msg) {
		if(instance==null) {
			Thread t = new Thread(new CommPrinter());
			t.start();
		}
		instance.write(msg);
    }
}
