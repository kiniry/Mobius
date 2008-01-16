class A /*#{ghost Object g}*/ {
  int x /*#guarded_by g*/;
}

public class C {
  public Object x;
  public A/*#{x}*/ a; // x should be final!
  public void m() {
    a.x = 0; // arguments are lazily checked!
  }
}

