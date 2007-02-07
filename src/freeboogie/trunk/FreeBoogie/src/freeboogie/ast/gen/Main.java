/** Public domain. */

package freeboogie.ast.gen;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

import freeboogie.util.Err;

/**
 * @author rgrig
 * @author reviewed by TODO
 */
public class Main {
  private static final Logger log = Logger.getLogger("freeboogie.ast.gen");
  
  // TODO: make it possible to override this from the command line
  private static String defaultBase = "Node";

  /**
   * Reads in a grammar file and uses that information to expand the macros in a
   * template file.
   * 
   * @param args <code>args[0]</code> is the grammar file and
   *          <code>args[1..]</code> are template files
   */
  public static void main(String[] args) {
    if (args.length == 0) 
      Err.fatal("Syntax: java freeboogie.ast.gen.Main grammar templates", 1);
    
    try {
      Handler logh = new FileHandler("ast_gen.log");
      logh.setFormatter(new SimpleFormatter());
      log.addHandler(logh);
      //log.setLevel(Level.ALL); // for debug
    } catch (IOException e) {
      System.err.println("I can't create a log file. Nevermind.");
    }

    Grammar grammar = null;
    try {
      AgParser agParser = new AgParser();
      agParser.setInputStream(new FileInputStream(args[0]));
      agParser.parseAg();
      grammar = agParser.getGrammar();
    } catch (IOException e) {
      Err.fatal("I can't read the abstract grammar.", 2);
    }
  }
}
