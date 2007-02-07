/** Public domain. */

package freeboogie.ast.gen;

/**
 * TODO: description
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class AgToken {

  /** The tokens in an AG. */
  public enum Type {
    /** enum */ ENUM,
    /** = */ EQ,
    /** : */ COLON,
    /** ; */ SEMICOLON,
    /** :> */ SUPERTYPE,
    /** ! */ BANG,
    /** ( */ LP,
    /** ) */ RP,
    /** , */ COMMA,
    /** identifier */ ID,
    /** whitespace */ WS,
    /** new-line */ NL,
    /** comment */ COMMENT,
    /** none of the above */ ERROR
  }
  
  /** The type of token. */
  public Type type;
  
  /** How it appears in the input file. */
  public String rep;
  
  /**
   * Initializes a token;
   * @param type the token type
   * @param rep the token representation in the input stream
   */
  public AgToken(Type type, String rep) {
    this.type = type;
    this.rep = rep;
  }
  
  /**
   * Returns whether this is a syntactically meaningful token.
   * @return whether this is a syntactically meaningful token
   */
  public boolean isGood() {
    return type != Type.COMMENT 
      && type != Type.WS
      && type != Type.NL;
  }
  
  /**
   * @param args
   */
  public static void main(String[] args) {
  // TODO Auto-generated method stub

  }

}
