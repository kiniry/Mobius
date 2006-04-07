package prover.exec.toplevel.stream;

public interface IStreamListener {
	public static int NORMAL=0;
	public static int ERROR = 0;
	public void append(int type, String str);
}
