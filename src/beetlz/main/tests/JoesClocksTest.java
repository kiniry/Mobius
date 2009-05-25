import main.Beetlz;

/**
 * 
 */

/**
 * @author evka
 *
 */
public class JoesClocksTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    final String path = "/Users/evka/Documents/final_year_project/" +
    "workspace/Clocks/src";
  

  String[] my_args = {//"-verbose",
                      "-userSettings", path + "/clocks/clocks_custom_settings.txt",
                      "-files", path, 
                      };
  
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
  

  }

}