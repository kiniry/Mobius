import main.Beetlz;

public class DebugTest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
	  System.out.println("****************** First run *********************");
	  System.out.println("**************** Files not found ******************");
	  System.out.println("******* No faults or errors, but verbose *********");
    
	  String[] my_args = {
        "-source", "both",
        "-verbose",
        //"-help",
        //"-userSettings", "tests/debug/custom.txt",
        "-files", "test", "test/dummy.bon", "test/dummy.java"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.debugParsing();
    checker.run();
    
    System.gc();
    
    String[] my_args2 = {
        "-help",
        };
    
    final Beetlz checker2 = new Beetlz(my_args2, System.err, System.out);
    
    System.gc();
    
    String[] my_args3 = {
        "-source", "java",
        "-skeleton",
        //"-help",
        //"-userSettings", "tests/debug/custom.txt",
        "-files", "test"
        };
    
    final Beetlz checker3 = new Beetlz(my_args3, System.err, System.out);
    checker3.run();
    
    System.gc();
    
    String[] my_args4 = {
        "-source", "java",
        "-skeleton",
        //"-help",
        //"-userSettings", "tests/debug/custom.txt",
        "-files", "test"
        };
    
    final Beetlz checker4 = new Beetlz(my_args4, System.err, System.out);
    checker4.run();
	}
	
}
