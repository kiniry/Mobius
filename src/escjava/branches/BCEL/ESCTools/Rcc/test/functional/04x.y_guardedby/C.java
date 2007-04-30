class A {
  public final Object y;
  public int x /*#guarded_by y*/;
}

public class C {
  private A a /*#guarded_by this*/;

  public synchronized void doit() {
    a.x = 0;    // lock y may not be held, nothing about this
    synchronized (a.y) {
      a.x = 1;  // should be ok
    }
  }
}
