public class C {
  public final Object a = new Object();
  public final Object b = new Object();

  public void m() {
    int x[/*#elems_guarded_by a*/];
    int y[/*#elems_guarded_by b*/];
    y = x;
  }
}

