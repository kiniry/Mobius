
public class C {
    public final Object o;
    String s[ /*# elems_guarded_by o */]  /*# guarded_by this */;
}


class F  {
    C b;
    
    public void  f() {
	b.s[3] = "asd";
	synchronized(b.o) {
	    synchronized(b) {
		b.s[3] = "asd";
		b.s[3] = "asd";
	    }
	}
	synchronized(b) {
	    b.s[3] = "asd";
	}
    }
}

class G {
    
    public final Object o, o1, o2;
    C b[ /*# elems_guarded_by o */][ /*# elems_guarded_by o1,o2 */];
    
    public void f() {
	synchronized(o) {
	    b[1] = null;
	    b[1][1] = null;
	    synchronized(o1) {
		synchronized(o2) {
		    b[1][1] = null;
		}
		b[1] = null;
		b[1][1] = null;
	    }
	}
	
	synchronized(o1) {
	    b[1] = null;
	    b[1][1] = null;
	}
    }
}

class gG {
    
    public final Object o, o1, o2;
    C b[ /*# elems_guarded_by o */][ /*# elems_guarded_by o1,o2 */];
    
    public void f() {
	synchronized(o) {
	      C b2[ /*# elems_guarded_by o */][ /*# elems_guarded_by o1,o2 */];
	    b2[1] = null;
	    b2[1][1] = null;
	    synchronized(o1) {
		synchronized(o2) {
		     C b3[ /*# elems_guarded_by o */][ /*# elems_guarded_by o1,o2 */];
		     b2 =  (C[ /*# elems_guarded_by o *//*# elems_guarded_by o *//*# elems_guarded_by o *//*# elems_guarded_by o */][ /*# elems_guarded_by o1,o2 */])b3;
		    b2[1][1] = null;
		}
		b[1] = null;
		b[1][1] = null;
	    }
	}
	
	synchronized(o1) {
	    b[1] = null;
	    b[1][1] = null;
	}
    }
}



class W {
    void foo() {
	final Object o;
	int x[/*# elems_guarded_by o */];
	int x2[/*# elems_guarded_by x */];
	x = x2;
	x2 = x;
	o = x;
    }
}
