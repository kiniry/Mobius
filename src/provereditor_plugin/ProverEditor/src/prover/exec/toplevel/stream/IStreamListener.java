package prover.exec.toplevel.stream;

public interface IStreamListener {
	public static int NORMAL = 1;
	public static int ERROR = 2;
	public void append(int type, String str);
}
