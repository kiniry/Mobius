package main;

public class List {
  public int i = 0;

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
