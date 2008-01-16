
public class C {
    String s  /*# guarded_by this */;
    String s1  /*# guarded_by this */;
}


/*# thread_local */
class F extends C {
    C b;
    String t /*# guarded_by b.s */;
    
    
    public void  f() {
        synchronized(b.s) {
            t = "asd";
        }
    }
}

/*# thread_shared */
class G {
    C g;
    static Object o;
}
