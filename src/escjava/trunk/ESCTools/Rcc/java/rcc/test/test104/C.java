
public class C {
    String s  /*# guarded_by this */;
    /*# requires this */ 
    public void  f() {
        s = "asd";
    }
}


class G extends C {
    static Object o /*# guarded_by G.o */;

    public void  i() {
        synchronized(o) { 
            o = o;
        }
    }
}
