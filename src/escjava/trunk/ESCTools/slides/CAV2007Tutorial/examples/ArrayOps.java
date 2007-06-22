public class ArrayOps {

  private /*@ spec_public @*/ Object[] a;

  //@ public invariant 0 < a.length;

  /*@ requires 0 < arr.length;
    @ ensures this.a == arr;
    @*/
  public void init(Object[] arr) {
    this.a = arr;
  }

  /*@ requires (\exists int i;
    @       0 <= i && i < a.length;
    @       a[i] == old);
    @ ensures a[\result] == nu
    @    && \old(a[\result] == old);
    @*/
  public int replace(Object old, Object nu) {
    for (int i = 0; i < a.length; i++) {
      if (a[i] == old) {
        a[i] == nu;
        return i;
      }
    }
    return -1;
  }
}
