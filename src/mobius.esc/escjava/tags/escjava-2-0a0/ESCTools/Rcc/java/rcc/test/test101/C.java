
public class C {
    String s;
    /*# requires this */ 
    public void  f() {
	s = "asd";
    }
}

class D extends C {
    /*# requires this, this */ 
    public void  f() {
	s = "asd";
    }
}

class E extends D {
    /*# requires this */ 
    public void  f() {
	s = "asd";
    }
}

class F extends C {
    public void  f() {
	s = "asd";
    }
}

class G extends C {
    static Object o;

    public void  i() {
	synchronized(o) { 
	    f();    
	}
    }
    public void  j() {
	synchronized(o) {
	    synchronized(this) {
		f();
	    }
	}
    }
    
    
    /*# requires this, o */
    public void  f() {
	s = "asd";
    }
}
