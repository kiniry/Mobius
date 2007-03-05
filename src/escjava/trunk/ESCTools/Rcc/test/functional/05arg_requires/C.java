class A {
  int x /*#guarded_by this*/;
}

public class C {
  public void doit(A a) /*#requires a*/ {
    a.x = 0;
    doit(a);
  }
}
