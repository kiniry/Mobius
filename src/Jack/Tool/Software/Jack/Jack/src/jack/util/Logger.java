package jack.util;


public class Logger{



	public final static NormalLogger err = new ErrorLogger();
	public final static NormalLogger warn = new WarningLogger();
	public final static NormalLogger out = new NormalLogger(System.out);
	public static NormalLogger get() {
		return out;
	}
}
