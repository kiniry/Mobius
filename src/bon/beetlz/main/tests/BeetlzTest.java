import main.Beetlz;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;


public class BeetlzTest extends TestCase {

  public void testComparison() {
    System.out.println("****************** test comparison *********************");
    String[] my_args = {
        "-source", "both",
        "-verbose",
        "-userSettings", "test/custom_file.txt",
        "-files", "test"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    //checker.debugParsing();
    checker.run();
    System.gc();
    assertTrue(true);
  }
  

  public void testBuggyComparison() {
    System.out.println("************* test comparison with bugs *****************");
    String[] my_args = {
        "-source", "both",
        //"-verbose",
        //"-userSettings", "tests/debug/custom.txt",
        "-files", "testBuggy"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    //checker.debugParsing();
    checker.run();
    System.gc();
    assertTrue(true);
  }
  
  
  public void testPrettyprintBON() {
    System.out.println("****************** pretty print BON *********************");
    String[] my_args = {
        "-source", "java",
        "-skeleton",
        "-files", "test"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
    System.gc();
    assertTrue(true);
  }
  
  public void testPrettyprintJava() {
    System.out.println("****************** pretty print Java *********************");
    String[] my_args = {
        "-source", "bon",
        "-skeleton",
        "-files", "test"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
    System.gc();
    assertTrue(true);
  }
  
  
  /*
  public void testFileNotFound() {
    System.out.println("****************** File not found *********************");
    String[] my_args = {
        "-source", "both",
        "-files", "tests/dummy.bon", "tests/dummy.java"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
    System.gc();
    assertTrue(true);
  }
  
  
  
  public void testBonParseError() {
    System.out.println("****************** BON parse error *********************");
    String[] my_args = {
        "-source", "bon",
        "-files", "tests/bonParseError.bon"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
    System.gc();
    assertTrue(true);
  }
  
  
  
  public void testJavaParseError() {
    System.out.println("****************** BON parse error *********************");
    String[] my_args = {
        "-source", "bon",
        "-files", "tests/javaParseError.java"
        };
    
    final Beetlz checker = new Beetlz(my_args, System.err, System.out);
    checker.run();
    System.gc();
    assertTrue(true);
  }
  
  */
  
  public static Test suite(){
    return new TestSuite(BeetlzTest.class);
  }
}
