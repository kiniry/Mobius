import main.Beetlz;

/**
 * @author evka
 *
 */
public class JoesLoggingTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    final String path = "/Users/evka/Documents/final_year_project/" +
    "workspace/Logging/src/mobius";
  

  String[] my_args = {//"-verbose", 
                      //"-noJML",
                      //"-specs", path + "/animal/jmlspecs.jar",
                      //"-noError",
                      "-skeleton", "/Users/evka/Documents/final_year_project/workspace/Logging",
                      "-skeletonOneFile",
                      "-noNullCheck",
                      //"-userSettings", path + "/custom_zoo.txt",
                      "-files", path, };
  
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
  

  }

}
