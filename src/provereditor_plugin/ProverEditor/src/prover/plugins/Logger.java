package prover.plugins;

import java.io.PrintStream;

/**
 * Logging utilities. 3 stream to write the different kind of messages.
 * @author J. Charles
 */
public class Logger {
	/** the error stream */
	public final static NormalLogger err = new ErrorLogger();
	/** the warning stream */
	public final static NormalLogger warn = new WarningLogger();
	/** the output stream */
	public final static NormalLogger out = new NormalLogger();

	
	public static final class ErrorLogger extends NormalLogger {

		public ErrorLogger() {
			super(System.err);
		}
		
		public void println(String str) {
			StackTraceElement [] ste = new Exception().getStackTrace();		
			super.println(ste[1] + ": " +str); 
		}

	}
	
	public static class NormalLogger extends PrintStream{
		public NormalLogger(PrintStream ps) {
			super(ps);
		}
		public NormalLogger() {
			this(System.out);
		}
		
		public void println(Object o, String str) {
			print(o.getClass());
			println(str);
		}
			
	}
	
	public static final class WarningLogger extends NormalLogger {
		public WarningLogger() {
			super(System.out);
		}

		public void println(String str) {
			StackTraceElement [] ste = new Exception().getStackTrace();		
			super.println(ste[1] + ": " +str); 
		}
	}
}
