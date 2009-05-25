


import main.Beetlz;

/**
 * Main class for the ConsistencyChecker.
 * @author Evka
 * @version 0.1
 */
public class PrettyTest {

  /**
   * Main method.
   * @param some_args arguments
   */
  public static void main(final String[] some_args) {
    final String path = "/Users/evka/Documents/final_year_project/" +
      "workspace/Beetlz/tests/zoo";
    final String dirPath = "/Users/evka/Documents/final_year_project/" +
    "workspace/SkeletonTest";
    final String pathWindows = "C:\\Users\\evka\\Documents\\final_year_project\\workspace\\Beetlz";

    String[] args = {"-source", "java", 
                     //"-pureBON",
                     //"-verbose",
                     "-skeleton", 
                     dirPath,
                     //"-skeletonOneFile",
                     //"-noNullCheck",
                    // "/Users/evka/Documents/final_year_project/workspace/SkeletonTest/src/zoo",
                     "-userSettings", path + "/custom_zoo.txt",
                     "-files", path};
    
      final Beetlz checker = new Beetlz(args, System.err, System.out);
      checker.run();
    
   
  }
}
