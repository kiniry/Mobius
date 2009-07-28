class A /*#{ghost Object a}*/ {
  int t /*#guarded_by a*/;
}

class B {
  final Object b;
  A/*#{b}*/ f /*#guarded_by this*/;
  synchronized void m() /*#requires b*/ {
    f.t = 1;
  }
}
