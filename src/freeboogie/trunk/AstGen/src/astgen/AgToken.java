package astgen;

/**
 * Represents an abstract grammar token.
 * 
 * @author rgrig 
 */
public class AgToken extends Token {

  /** The tokens in an AG. */
  public enum Type {
    ENUM,
    EQ,
    COLON,
    SEMICOLON,
    SUPERTYPE,
    BANG,
    LP,
    RP,
    COMMA,
    ID,
    WS,
    NL,
    COMMENT,
    ERROR
  }
  
  /** The type of token. */
  public Type type;
  
  /**
   * Initializes a token.
   * @param type the token type
   * @param rep the token representation in the input stream
   */
  public AgToken(Type type, String rep) {
    super(rep);
    this.type = type;
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
}
