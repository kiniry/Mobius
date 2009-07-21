package freeboogie.tc;

import java.io.FileNotFoundException;
import java.io.IOException;

import genericutils.Err;
import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import freeboogie.ast.Declaration;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;

/**
 * Used for testing the typechecker.
 * It prints a list of identifiers and the place where they are defined.
 * It also prints errors if there are name clashes.
 *
 * @author rgrig 
 */
public final class Main {
  private Main() { /* forbid instantiation */ }

  /** Test a bit the package.
   * @param args the files to process
   * @throws IOException 
   * @throws RecognitionException 
   */
  public static void main(String[] args) throws IOException, RecognitionException {
    TypeChecker tc = new TypeChecker();
    for (int i = 0; i < args.length; ++i) {
      try {
        System.out.println("=== " + args[i] + " ===" );
        FbLexer lexer = new FbLexer(new ANTLRFileStream(args[i]));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FbParser parser = new FbParser(tokens);
        parser.fileName = args[i];
        Declaration d = parser.program();
        if (d != null) {
          // parsing was OK
          for (FbError e : tc.process(d)) Err.error(e.toString());
        }
      } catch (FileNotFoundException e) {
        Err.error("I couldn't read from " + args[i] + ". Nevermind.");
      }
    }
  }

}
