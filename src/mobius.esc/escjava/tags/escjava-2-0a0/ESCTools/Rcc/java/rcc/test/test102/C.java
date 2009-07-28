
public class C {
    String s  /*# guarded_by this */;
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
    String s  /*# guarded_by this */;
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
    static Object o /*# guarded_by G.o */;

    public void  i() {
	synchronized(G.o) { 
	    f();
	    G.o = G.o;
	}
    }
    public void  j() {
	synchronized(G.o) {
	    synchronized(this) {
		f();
		G.o = G.o;
	    }
	}
    }
    
    
    /*# requires this, G.o */
    public void  f() {
	s = "asd";
	G.o = G.o;
    }
}
