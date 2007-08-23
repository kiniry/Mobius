/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Aug 26, 2004
 */
package pluginlib;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;

import org.eclipse.core.runtime.ILog;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

/**
 * This class provides a uniform interface for logging informational
 * and error messages.  Do not use it for messages to the user in the
 * course of normal interaction with the tool.  Instead, the 
 * informational output is for debugging and tracing purposes; the
 * error output is for internal error reporting (and not, for
 * example, for reports to users about erroneous user input).
 * <P>
 * Log.on is a boolean flag to be used in user code as a convenience
 * test, as in  <BR>
 *        if (Log.on) Log.log(msg);  <BR>
 * The test happens before the method call.
 * <P>
 * The location of the output is determined by the various options:<BR>
 * Informational output:					<BR>
 * 	in the console if Log.useConsole		<BR>
 *  in System.out if  !Log.useConsole		<BR>
 *  in the Eclipse error log if Log.alsoLogInfo <BR>
 * 											<BR>
 * Error output:							<BR>
 * 	in the console if Log.useConsole		<BR>
 *  in System.out if  !Log.useConsole		<BR>
 *  in the Eclipse error log always			<BR>
 *  										<BR>
 * Note that output sent to System.out may be lost depending on
 * the manner in which Eclipse is started (it might also end up
 * in a command terminal or in a parent Console during plugin
 * development).
 * 
 * @author David Cok
 *
 */
public class Log {
	
	/** Holds a current value for the log object, for convenience */
	public static Log log = null;

	/** A flag used to record whether or not to output tracing 
	 *  information.
	 */
	public static boolean on = false;
	
	/** Creates a Log and sets the current log object
	 * 
	 * @param consoleName The name of the console to be logged to
	 * @param plugin The plugin object using this log
	 */
	//@ requires consoleName != null;
	//@ modifies log;
	//@ ensures log != null && \fresh(log);
	//@ ensures log.consoleName == consoleName;
	public static void createLog(String consoleName, Plugin plugin) {
		log = new Log(consoleName,plugin);
	}

	/**
	 * Initializes any internal state of the log, e.g. based on
	 * stored preferences or properties.
	 * 
	 * @param on Sets (globally) whether anything is desired to be logged or not.
	 * 			This is simply to be tested in code prior to calling log() or errorlog(),
	 * 			to avoid the method invocation when logging is off, as in
	 * 				if (Log.on) Log.log(msg);
	 * @param useConsole Sets whether logged output is sent to System.out or to the Eclipse console
	 * @param alsoLogInfo Sets whether informational output (via log()) should be sent to the system
	 * 			error log as well; material sent to errorlog() is always sent to the error log.
	 */
	//@ requires log != null;
	//@ modifies Log.on, log.useConsole, log.alsoLogInfo;
	//@ ensures Log.on == on;
	//@ ensures log.useConsole == useConsole;
	//@ ensures log.alsoLogInfo == alsoLogInfo;
	public static void initializeState(boolean on, boolean useConsole, boolean alsoLogInfo) {
		boolean b = Log.on;
		Log.on = on;
		if (log == null) {
			// Internal error - no log yet defined
			// FIXME
			return;
		}
		log.init(useConsole,alsoLogInfo);
		if (b != Log.on) Log.log("Logging is now " +
				(Log.on ? "on" : "off"));
	}
	
	/**
	 * Records an informational message to the current log
	 * @param msg The message to log
	 */
	//@ requires msg != null;
	//@ modifies log.content;
	public static void log(String msg) { log.ilog(msg); }
	
	/**
	 * Records an error message to the current log
	 * @param msg The message to log
	 * @param e An associated exception (may be null)
	 */
	//@ requires msg != null;	
	//@ modifies log.content;
	public static void errorlog(String msg, Throwable e) {
		log.ierrorlog(msg,e);
	}
	
	/**
	 * Creates a PrintStream that, when written to, writes to the Eclipse Console
	 * of the current log object
	 * 
	 * @return a PrintStream connected to the Eclipse Console
	 */
	//@ requires log != null;
	//@ pure
	public static PrintStream logPrintStream() {
		return log.consolePrintStream();
	}

	//==============================================================

	/** Creates a new Log utility object
	 * 
	 * @param consoleName The name of the console to be logged to
	 * @param plugin The plugin object using this log
	 */
	//@ requires consoleName != null;
	//@ requires plugin != null;
	//@ modifies \nothing;
	//@ ensures \result.consoleName == consoleName;
	private Log(String consoleName, Plugin plugin) {
		this.consoleName = consoleName;
		this.pluginLog = plugin.getLog();
		this.pluginID = plugin.getBundle().getSymbolicName();
	}
	
	// This model variable models the content of the material
	// sent to the log.
	//@ model public String content;
	
	/** The name of the console that this plugin writes to. */
	//@ constraint \not_modified(consoleName);
	//@ invariant consoleName != null;
	//@ spec_public
	private String consoleName;
	
	/** The ILog of the plugin that this Log object connects to */
	//@ constraint \not_modified(pluginLog);
	//@ invariant pluginLog != null;
	//@ spec_public
	private ILog pluginLog;
	
	/** The id of the plugin using this log */
	//@ constraint \not_modified(plugiID);
	//@ invariant pluginID != null;
	//@ spec_public
	private String pluginID;
	
	// TODO: Perhaps provide
	// a way to introduce other logging mechanisms.  One could
	// argue that the various options allowed here should just
	// be instances of different logging mechanisms.  That is a
	// degree of freedom we don't need right at the moment, though
	// it does make for a nice modular design.
	
	/** If true, put output to the console; if false, put output
	 *  to System.out.
	 */
	public boolean useConsole = true;
	
	/** If true, then informational output is recorded in the
	 *  system log; if false, then it is not.
	 */
	public boolean alsoLogInfo = false;
	
	/** Cached value of the MessageConsole object */
	private MessageConsole console = null;
	//@ private constraint \old(console) != null ==> \not_modified(console);
	
	/** Cached value of the stream to use to write to the console */
	private MessageConsoleStream stream = null;
	//@ private constraint \old(stream) != null ==> \not_modified(stream);
	
	/**
	 * Initializes any internal state of the log, e.g. based on
	 * stored preferences or properties.
	 * 
	 * @param useConsole Sets whether logged output is sent to System.out or to the Eclipse console
	 * @param alsoLogInfo Sets whether informational output (via log()) should be sent to the system
	 * 			error log as well; material sent to errorlog() is always sent to the error log.
	 */
	public void init(boolean useConsole, boolean alsoLogInfo) {
		this.useConsole = useConsole;
		this.alsoLogInfo = alsoLogInfo;
	}

	
	/** Creates, if necessary, and returns an instance of
	 *  the stream to use to write to the console
	 * @return The stream value to use
	 */
	//@ ensures \result != null;
	public MessageConsoleStream getConsoleStream() {
		if (console == null) {
			IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
			IConsole[] existing = consoleManager.getConsoles();
			for (int i=0; i<existing.length; ++i) {
				if (existing[i].getName().equals(consoleName)) {
					console = (MessageConsole)existing[i];
					break;
				}
			}
			if (console == null) {
				console = new MessageConsole(consoleName,null);
				consoleManager.addConsoles(new IConsole[]{console});
			}
			stream = console.newMessageStream();
		}
		return stream;
	}
	
	/** Color to use for error messages */
	// FIXME - should get this color from the system preferences
	static final private Color errorColor = new Color(null,255,0,0);
	
	/**
	 * Records an informational message 
	 * @param msg The message to log
	 */
	//@ requires msg != null;
	//@ modifies content;
	public void ilog(String msg) {
		if (useConsole) {
			getConsoleStream().println(msg);
		} else {
			System.out.println(msg);
		}
		// Also write it to the log file, if requested.
		if (alsoLogInfo) {
			pluginLog.log(
				new Status(Status.INFO, 
							pluginID,
							Status.OK, msg, null));
		}
	}
	
	
	/**
	 * Records an error message
	 * @param msg The message to log
	 * @param e An associated exception (may be null)
	 */
	//@ requires msg != null;
	//@ modifies content;
	public void ierrorlog(String msg, Throwable e) {
		// Always put errors in the log
		pluginLog.log(
				new Status(Status.ERROR, 
						pluginID,
						Status.OK, msg, e));
		if (useConsole) {
			MessageConsoleStream cs = getConsoleStream();
			Color c = cs.getColor();
			cs.setColor(errorColor);
			cs.println(msg);
			cs.setColor(c);
		} else {
			// We use System.out instead of System.err because otherwise
			// it seemed the output was not flushed/interleaved correctly
			// Perhaps some flushing would help ?? FIXME
			System.out.println(msg);
			if (e != null) e.printStackTrace(System.out);
		}
	}
	
	/**
	 * Creates a PrintStream that, when written to, writes to the Eclipse Console
	 * of the current log object
	 * 
	 * @return a PrintStream connected to the Eclipse Console
	 */
	public PrintStream consolePrintStream() {
		return new PrintStream(new StreamToConsole(getConsoleStream()));
	}
	
	/**
	 * This class is an OutputStream that, when written to, writes
	 * the data to the Eclipse Console supplied 
	 * in the constructor.  
	 * This requires converting from
	 * the byte data written to the Stream into character data that is
	 * written to a MessageConsole; thus a specific Charset is required.
	 * 
	 * @author David R. Cok
	 */
	public static class StreamToConsole extends OutputStream {
		protected ByteBuffer bb = ByteBuffer.allocate(2000);
		protected char[] input = new char[1];
		protected CharBuffer output = CharBuffer.allocate(2000);
		protected char[] outputchar = new char[2000];
		protected int len;
		protected CharsetDecoder decoder;
		
		/** The output console, set by the constructor. */
		//@ constraint \not_modified(console);
		//@ invariant console != null;
		protected MessageConsoleStream console;
		
		/**
		 * Constructs an OutputStream that is connected to the 
		 * given console.
		 * @param console The console to write to via the OutputStream
		 */
		public StreamToConsole(MessageConsoleStream console) {
			// FIXME - should use default charset for System.out
			// or set the charset from an argument
			decoder = Charset.forName("UTF-8").newDecoder();
			this.console = console;
		}

		// This implementation does not use the charset, because I
		// can't get the decoder to work in the code below.  FIXME
		public void write(int b) {
			outputchar[0] = (char)b;
			len = 1;
			dump(false);
		}
		
		public void write(byte[] b,int off, int len) {
			int n = len;
			while (true) {
				if (n > outputchar.length) n = outputchar.length;
				for (int k=0; k<n; ++k) outputchar[k] = (char)b[off+k];
				this.len = n;
				dump(false);
				if (n == len) return;
				off += n;
				len -= n;
			}
		}

		/**
		 * This writes everything from the outputchar buffer to the 
		 * Console
		 * @param end true if the stream should be flushed
		 */
		private void dump(boolean end) {
			if (len == 0) return;
			console.print(new String(outputchar,0,len));
			len = 0;
		}

//		public void write(int b) throws IOException {
//			bb.put((byte)b);
//			dump(false);
//		}
//		
//		public void write(byte[] b,int off, int len) throws IOException {
//			bb.put(b,off,len);
//			dump(false);
//		}
		
//		private void dump(boolean end) {
//			CoderResult cr;
//			do {
//				cr = decoder.decode(bb,output,end);
//				System.out.println("CR " + cr.toString());
//				int len;
//				while ((len = 7) > 0) {
//					if (len > outputchar.length) len = outputchar.length;
//					output.get(outputchar,0,len);
//					System.out.println("OUT " + new String(outputchar,0,len));
//					//getConsoleStream().print(new String(outputchar,0,len));
//				}
//				output.compact();
//			} while (false && cr.isOverflow());
//			bb.compact();
//		}
		
		public void flush() throws IOException {
			dump(true);
			//decoder.flush(output);
		}
		
		public void close() {
			bb = null;
			output = null;
			decoder = null;
		}
	}
}

