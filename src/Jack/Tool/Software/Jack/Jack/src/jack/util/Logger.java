package jack.util;

import java.io.PrintStream;

public class Logger extends PrintStream {

	private static Logger instance = new Logger(System.out);


	public final static Logger err = new ErrorLogger();
	public final static Logger warn = new WarningLogger();
	public final static Logger out = new Logger(System.out);
	
	public Logger(PrintStream ps) {
		super(ps);
	}
	
	

	public static Logger get() {
		return instance;
	}
	
//	public void println(String c) {
////		throw new IllegalArgumentException(""+ c);
//		super.println(c);
//	}
	
	public void printlnWarning(String str) {
		StackTraceElement [] ste = new Exception().getStackTrace();		
		err.println(ste[1] + ": " +str); 
	}
	
	public void printlnError(Object o, String str) {
		err.print(o.getClass() + ": " +str);
	}
	
	public void println(Object o, String str) {
		print(o.getClass());
		println(str);
	}
	
	private static class WarningLogger extends Logger {
		public WarningLogger() {
			super(System.out);
		}

		public void println(String str) {
			StackTraceElement [] ste = new Exception().getStackTrace();		
			super.println(ste[1] + ": " +str); 
		}
	}
	
	private static class ErrorLogger extends Logger {

		public ErrorLogger() {
			super(Logger.err);
		}
		
		public void println(String str) {
			StackTraceElement [] ste = new Exception().getStackTrace();		
			super.println(ste[1] + ": " +str); 
		}

	}
}
