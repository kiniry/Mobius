package mobius.bico;

import java.io.IOException;
import java.security.Permission;

/**
 * The main class to launch bico!
 * @author J. Charles (julien.charles@inria.fr),
 *         P. Czarnik (czarnik@mimuw.edu.pl)
 */
public final class Main {
  /** BICO version 0.5. */
  public static final String WELCOME_MSG = "BICO version 0.5";
  
  /**
   * Does nothing.
   */
  private Main() {
    
  }
  
  /**
   * Bico main entry point.
   * @param args the program arguments
   * @throws IOException if the is an error while creating the files
   */
  public static void main(final String[] args) throws IOException {
    System.out.println(WELCOME_MSG);
    System.setSecurityManager(new SecurityManager() {
      public void checkPermission(final Permission perm) {
      }
    });
    Executor exec;
    try {
      exec = new Executor(args);
    } 
    catch (IllegalArgumentException e) {
      System.err.println(e.getMessage());
      System.err.println("(try java -jar bico.jar help)");
      return;
    }
    try {
      exec.start();
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
      System.err.println(e.getMessage() + "\n" +
          "It was specified as a file to load... it should be in the class path!");
    }
  }
}
