class A/*#{ghost Object a}*/ {
  int x /*#guarded_by a*/;
}

public class C/*#{ghost Object b}*/ {
  public void doit(A/*#{b}*/ a) /*#requires b*/ {
    a.x = 0;
    doit(a);
  }
}
