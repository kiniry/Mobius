
public class C {
    final String s  /*# guarded_by this */;
    String t  /*# guarded_by this, s */;
}

class D {
    public void  f() {
        C c = new C();
        synchronized(c) {
            c.t = "1";
                    synchronized(c.s) {
            c.t = "2";
                }
                
        }
    }
    
}

class E {
    final Object o;
    String c /*# guarded_by o */;
}

class EE {
    final Object o;
    E e /*# guarded_by o */;
}

class F {
    EE e;
    void f() {
        synchronized(e) {
            synchronized(e.o) {
                synchronized(e.e.o) {
                e.e.c = "asd";
                }
            }
        }
    }
}



