
public class C {
    String s  /*# guarded_by this */;
    String s1  /*# guarded_by this */;
}


class F extends C {
    C b;
    String t /*# guarded_by b.s */;
    
    
    public void  f() {
	synchronized(b.s) {
	    t = "asd";
	}
    }
}

