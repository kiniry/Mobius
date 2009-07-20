/**
 * 
 */
package jack.util;

public final class ErrorLogger extends NormalLogger {

	public ErrorLogger() {
		super(System.err);
	}
	
	public void println(String str) {
		StackTraceElement [] ste = new Exception().getStackTrace();		
		super.println(ste[1] + ": " +str); 
	}

}