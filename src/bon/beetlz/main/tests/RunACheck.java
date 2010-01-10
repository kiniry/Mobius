import main.Beetlz;

/**
 * Class specialised for testing with the example code inside the project in Eclipse.
 * This will do a sort of 'regression' test. The first run should be without errors,
 * there will be plenty in the second run.
 * It will determine the location of the test code based on the classpath.
 */
public class RunACheck {

	/**
	 * @param args
	 */
	public static void main(String[] args) {		
		String current = System.getProperty("java.class.path");
		
		String[] parts = current.split("[:;]");
		
		String path = parts[0];
		
		System.out.println("This is a regression test. First run should not produce any errors.\n" +
				"The second run produces 25 Java errors, 2 Java warnings, 9 JML errors and 9 JML warnings." +
				"It runs the check both ways.");
		
		if(path.endsWith("/bin")|| path.endsWith("\\bin")) {
			path = path.substring(0, path.length()-3);
			{
				String[] my_args = {
						"-source", "both",
		                "-userSettings", path + "examples/zoo/custom_zoo.txt",
		                "-files", path + "examples/zoo"
		                };
				
				System.out.println("****************** First run *********************");
				final Beetlz checker = new Beetlz(my_args, System.err, System.out);
				//checker.debugParsing();
			  //  checker.run();
			}
			
			
			{
				String[] my_args = {
						"-source","both",
		                "-userSettings", path + "examples/zoo_faults/custom_zoo.txt",
		                "-files", path + "examples/zoo_faults"
		                };
				
				System.out.println("****************** Second run *********************");
				final Beetlz checker = new Beetlz(my_args, System.err, System.out);
				checker.debugParsing();
			  checker.run();
			}
			
		} else {
			System.err.println("Error: classpath has wrong format.");
		}
		

	}

}
