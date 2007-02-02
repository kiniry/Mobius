/** Public domain. */

package freeboogie.ast.gen;

import java.io.IOException;
import java.io.InputStream;
import java.util.logging.Logger;

import freeboogie.util.Err;

/**
 * Used for flow control in {@code AgParser}.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("serial")
class EofReached extends Exception {
  // only the type is important
}

/**
 * A hand-crafted parser for abstract grammar (AG) textual descriptions.
 * See packages {@link freeboogie.ast} and {@link freeboogie.ast.gen}
 * for examples. A reason why this is handcrafted is that I want to
 * compare the experience of writing it with the experience of writing
 * the BoogiePL parser using ANTLR. It should also be not too hard since
 * the input language is <i>really</i> simple. On the other hand I can 
 * explore the design space of a parse more, for example by giving really
 * custom error messages and hints of what might be wrong.
 * 
 * TODO Idea: in order to improve error messages I could log them,
 * ask users to send the logs and do an empirical study of typical mistakes.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class AgParser {
  
  private static final Logger log = Logger.getLogger("freeboogie.ast.gen"); 
  
  private AgLexer lexer;
  private Grammar grammar;
  
  /**
   * Creates an AG parser.
   */
  public AgParser() {
    grammar = new Grammar();
  }
  
  /**
   * Sets the input stream for the next parsing operation. 
   * @param stream the input stream
   */
  public void setInputStream(InputStream stream) {
    lexer = new AgLexer(new CharStream(stream));
  }
  
  /** 
   * This will read in an AG from the input stream. 
   * @throws IOException if thrown by the underlying stream 
   * */
  public void parseAg() throws IOException {
    try {
      while (true) parseStatement();
    } catch (EofReached e) {
      // normal finish
    }
  }
  
  /**
   * Gets the grammar. Initially it is empty.
   * @return the grammar
   */
  public Grammar getGrammar() {
    Err.notImplemented();
    return null;
  }
  
  private void parseStatement() throws IOException, EofReached {
    AgToken t = nextToken();
    if (t.type != AgToken.Type.ID) {
      skipStatement();
      return;
    }
    
    String className = t.rep;
    t = nextToken();
    if (t.type == AgToken.Type.EQ) {
      // parse "class = members"
      Err.notImplemented();
    } else if (t.type == AgToken.Type.COLON) {
      // parse "class : spec"
      Err.notImplemented();
    } else if (t.type == AgToken.Type.SUPERTYPE) {
      // parse "class :> derived"
      Err.notImplemented();
    } else {
      skipStatement();
      return;
    }
    
    Err.notImplemented();
  }
  
  private void skipStatement() {
    // TODO: report error and do the skipping to the first semicolon
    Err.notImplemented();
  }
  
  private AgToken nextToken() throws IOException, EofReached {
    AgToken token = lexer.nextGood();
    if (token == null) throw new EofReached();
    return token;
  }
  
  /**
   * For testing purposes. (TODO)
   * @param args
   */
  public static void main(String[] args) {
  // TODO Auto-generated method stub

  }
}
