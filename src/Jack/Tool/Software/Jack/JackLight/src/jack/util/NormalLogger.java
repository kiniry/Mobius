package jack.util;

import java.io.PrintStream;

public class NormalLogger extends PrintStream{
	public NormalLogger(PrintStream ps) {
		super(ps);
	}
	
	
	public void println(Object o, String str) {
		print(o.getClass());
		println(str);
	}
		
}
