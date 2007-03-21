class A {
  public static final Object x = new Object();
}

class B /*#{ghost Object g}*/ {
  int f /*#guarded_by g*/;
}

public class C extends B/*#{A.x}*/ {
  public void m() {
    f = 0;    // A.x not held!
    synchronized (A.x) {
      f = 0;  // OK
    }
  }
}

