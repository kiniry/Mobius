public class C {
  final String s  /*# guarded_by this */;
  String t  /*# guarded_by this, s */;
}

class D {
  public void  f() {
    C c = new C();
    synchronized(c) {
      c.t = "1";   // should give a warning
      synchronized(c.s) {
        c.t = "2";
      }
      
    }
  }
}





