package jml2bml.utils;
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
   * Hidden constructor.
   */
  private UniqueIndexGenerator() {
  }
  /**
   * Generates new index.
   * @return generated index
   */
  public static int getNext() {
    index++;
    return index;
  }

}
