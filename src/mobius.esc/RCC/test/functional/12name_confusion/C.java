class D /*# {ghost Object g} */ {
  public int a /*# guarded_by g */;
}

class F {
  public static final Object d = new Object();
}

class C {
  D/*#{F.d}*/ dd;
  void f() {
    synchronized(F.d) {
      dd.a = 2; // should be fine
    }
  }
}

class G /*# {ghost Object o}  */ {
  D/*#{o}*/ dd /*#guarded_by this*/;
  synchronized void f() /*# requires o */{
    dd.a = 2; // should be fine
  }
}
