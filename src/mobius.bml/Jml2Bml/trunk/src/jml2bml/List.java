package jml2bml;

public class List {
  public int i;

  public int increase() {
    i++;
    return i;
  }

  public void loop() {
    int j = 0;
    /*@ loop_invariant i < 5;
     *
     */
    while (increase() < 5) {
      j = i;
    }
    System.out.println(j);
  }
}
