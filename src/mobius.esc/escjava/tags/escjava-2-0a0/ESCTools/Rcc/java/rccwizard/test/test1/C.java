class CB {

    Object a = new Object();

    Object b;
    Object d;

    void m() {
	synchronized(a) {
	    b = new Object();
	}
	d = a;
    }

    public static void main(String[] args) {
	(new CB()).m();
    }
}


class CC {
    CB b;
    public void run() {
	b.m();
	b = new CB();
    }
}



class CCC extends Thread {
    static CCC a;
    public void run() {
	b.run();
    }
    CC b;
}


