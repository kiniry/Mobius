import main.Beetlz;

public class DebugTest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {		
		String[] my_args = {
						"-source", "both",
						//"-help",
		                "-userSettings", "tests/debug/custom.txt",
		                "-files", "tests/debug"
		                };
				
		System.out.println("****************** First run *********************");
		final Beetlz checker = new Beetlz(my_args, System.err, System.out);
		//checker.debugParsing();
		checker.run();
		
	}
}
