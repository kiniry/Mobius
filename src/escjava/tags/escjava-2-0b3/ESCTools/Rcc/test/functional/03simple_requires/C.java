public class C {
  private final Object lock;
  private int data /*#guarded_by lock*/;

  public void doit() /*#requires lock*/  {
    data = 0;
  }
}
