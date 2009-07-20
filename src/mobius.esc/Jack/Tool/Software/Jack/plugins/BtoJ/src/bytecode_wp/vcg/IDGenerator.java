package bytecode_wp.vcg;

public class IDGenerator {

	private static int random = 0;
	
	public static Integer getInt() {
		return new Integer(random++);
	}
	
}