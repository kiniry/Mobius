public class C {
  public static final Object a = new Object();
  public static final Object b = new Object();
  
  int x/*#guarded_by a*/;
  int y/*#guarded_by a,b*/;

  void f() {
    synchronized (a) {
      synchronized(b) {
        x = y;
        y = x;
      }
    }
  }
}

