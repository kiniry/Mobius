/** Public domain. */

package freeboogie.ast.gen;

/**
 * TODO: description
 *
 * @author rgrig 
 * @author reviewed by TODO
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

  /**
   * TODO tests
   * 
   * @param args
   */
  public static void main(String[] args) {
    // TODO Auto-generated method stub
  }

}
