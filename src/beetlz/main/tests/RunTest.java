import main.Beetlz;

/**
 * 
 */

/**
 * @author evka
 *
 */
public class RunTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    final String path = "/Users/evka/Documents/final_year_project/" +
    "workspace/Beetlz/tests/zoo";
  final String windowsPath = "C:\\Users\\evka\\Documents\\final_year_project\\workspace\\Beetlz\\tests\\zoo";

  String[] my_args = {//"-verbose", 
                      //"-noJML",
                      //"-noJava",
                      //"-specs", path + "/animal/jmlspecs.jar",
                      //"-noError",
                      //"-noWarning",
                      //"-noNullCheck",
                      // "-help",
                      "-userSettings", path + "/custom_zoo.txt",
                      "-files", path, 
                      "/Users/evka/Documents/final_year_project/workspace/Beetlz/tests/defaultpackage/ZooClass.java", 
                      };
  /*String[] my_args = {//"-verbose", 
      //"-noJML",
      //"-noJava",
      //"-specs", path + "/animal/jmlspecs.jar",
      //"-noError",
      //"-noWarning",
      //"-noNullCheck",
      // "-help",
      "-userSettings", windowsPath + "/custom_zoo.txt",
      "-files", windowsPath, 
      "/Users/evka/Documents/final_year_project/workspace/Beetlz/tests/defaultpackage/ZooClass.java", 
      };
  */
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
  

  }

}
