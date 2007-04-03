/** Public domain. */

package freeboogie.parser;

import java.io.IOException;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

/**
 * Generate a pretty print of the AST constructed during parsing.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Main {

  /**
   * @param args
   * @throws RecognitionException 
   */
  public static void main(String[] args) throws IOException, RecognitionException {
    FbLexer lexer = new FbLexer(new ANTLRInputStream(System.in));
    CommonTokenStream tokens = new CommonTokenStream(lexer);
    FbParser parser = new FbParser(tokens);
    parser.program();
  }
}
