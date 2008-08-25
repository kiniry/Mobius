class A {
  int x /*#guarded_by this*/;
}

public class C {
  public void doit(final A a) /*#requires a*/ {
    a.x = 0;
    doit(a);
  }

  public void go() {
    A b = new A();
    synchronized (b) {
      doit(b);
    }
  }
}
