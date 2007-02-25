/*#thread_shared*/ public class C {
  private Object lock;
  private int data /*#guarded_by lock*/;

  public void doit() {
    data = 1;
    synchronized (lock) {
      data = 0;
    }
  }
}
