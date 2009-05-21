package astgen;

/**
 * A generic token. It has a string representation.
 *
 * @author rgrig 
 */
public abstract class Token {

  /** How it appears in the input file. */
  public String rep;
  
  /**
   * Initializes the token with a given textual representation.
   * This is used by {@code TokenLocation}.
   * 
   * @param rep The textual representation of the token
   */
  public Token(String rep) {
    this.rep = rep;
  }
}
