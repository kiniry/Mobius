import main.Beetlz;

/**
 * 
 */

/**
 * @author evka
 *
 */
public class FaultyTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    final String path = "/Users/evka/Documents/final_year_project/" +
    "workspace/Beetlz/tests/zoo_faults";
  

  String[] my_args = {//"-verbose", 
                      //"-noJML",
                      //"-specs", path + "/animal/jmlspecs.jar",
                      "-userSettings", path + "/custom_zoo.txt",
                      "-files", path};
  
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
  

  }

}
