import main.Beetlz;

/**
 * Class specialised for testing with the example code inside the project in Eclipse.
 * It will determine the location of the test code based on the classpath.
 */
public class RunATest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {		
		String current = System.getProperty("java.class.path");
		String[] parts = current.split("[:;]");
		
		String path = parts[0];
		if(path.endsWith("/bin")|| path.endsWith("\\bin")) {
			path = path.substring(0, path.length()-3);
			
			String[] my_args = {
					//"-verbose", 
	                //"-noJML",
	                //"-noJava",
					//"-noError",
	                //"-noWarning",
	                //"-noNullCheck",
	                // "-help",
	                
	                "-userSettings", path + "tests/zoo/custom_zoo.txt",
	                "-files", path + "tests/zoo"
	                };
			
			final Beetlz checker = new Beetlz(my_args, System.err, System.out);
		    checker.run();
			
		} else {
			System.err.println("Error: classpath has wrong format.");
		}
		

	}

}
