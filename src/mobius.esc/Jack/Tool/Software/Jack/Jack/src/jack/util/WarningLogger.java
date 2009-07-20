/**
 * 
 */
package jack.util;

public final class WarningLogger extends NormalLogger {
	public WarningLogger() {
		super(System.out);
	}

	public void println(String str) {
		StackTraceElement [] ste = new Exception().getStackTrace();		
		super.println(ste[1] + ": " +str); 
	}
}