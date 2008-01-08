package jml2bml.engine;
/**
 *
 * @author Jedrek (fulara@mimuw.edu.pl)
 *
 * Generates unique index (for bounded variables)
 * @version 0-1
 *
 */
public final class UniqueIndexGenerator {
  /**
   * Previous index value.
   */
  private static int index;
  /**
   * Generates new index.
   * @return generated index
   */
  public static int getNext() {
    index++;
    return index;
  }
  
  /**
   * Hidden constructor.
   */
  private UniqueIndexGenerator(){}
}
