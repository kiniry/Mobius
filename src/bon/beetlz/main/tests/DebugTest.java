import main.Beetlz;

public class DebugTest { 

	/**
	 * @param args
	 */
	public static void main(String[] args) {
	  System.out.println("****************** Debug Test *********************");
	  String[] my_args = {
        "-source", "bon", 
        "-skeleton",
        //"-help",
        "-verbose",
        //"-noJML",
        //"-userSettings", "tests/debug/custom.txt",
        "-files", "tests/debugCluster/DebugClass.java", "tests/debugCluster/debug.bon", "tests/debugCluster/Test.java"
        //"-files", "tests/debugCluster/DebugClass.java"
        //"-files", "tests/debugCluster"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    //checker.debugParsing();
    checker.run(); 
        
	}
	
}
