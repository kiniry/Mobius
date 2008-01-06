package jml2bml.engine;

public class UniqueIndexGenerator {
  private static int index = 0;
  public static int getNext(){
    index++;
    return index;
  }
}
