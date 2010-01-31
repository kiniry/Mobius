import main.Beetlz;

public class DebugTest { 

	/**
	 * @param args
	 */
	public static void main(String[] args) {
	  System.out.println("****************** Debug Test *********************");
	  String[] my_args = {
        "-source", "both", 
        "-skeleton",
        //"-help",
        //"-verbose",
        //"-userSettings", "tests/debug/custom.txt",
        "-files", "tests/debug/Debug.java", "tests/debug/debug.bon"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.debugParsing();
    checker.run();
        
	}
	
}
