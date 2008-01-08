package jml2bml.engine;
/**
 * 
 * @author Jedrek (fulara@mimuw.edu.pl)
 *
 */
public class UniqueIndexGenerator {
  private static int index = 0;
  public static int getNext() {
    index++;
    return index;
  }
}
