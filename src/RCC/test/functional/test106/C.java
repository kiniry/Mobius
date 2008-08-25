
public class C {
    final String s  /*# guarded_by this */;
    String s1  /*# guarded_by this */;
    public final static String t;
    
}


class F extends C {
    C b;
    String t /*# guarded_by b.s */;
    String tt /*# guarded_by b.s1, C.t, C.class */;
    
    
    public void  f() {
        synchronized(C.class) {
            tt = "123";
        }
        synchronized(b.s) {
            t = "asd";
        }
    }
}

