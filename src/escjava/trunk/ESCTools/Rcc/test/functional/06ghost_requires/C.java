class A/*#{ghost Object a}*/ {
  int x /*#guarded_by a*/;
}

public class C {
  public void doit(A/*#{b}*/ a) /*#requires b*/ {
    a.x = 0;
    doit(a);
  }
  public void go() {
    A c = new A();
    synchronized(b) {
      doit(b);
    }
  }
}
