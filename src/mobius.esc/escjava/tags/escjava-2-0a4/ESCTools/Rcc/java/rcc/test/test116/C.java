
class D /*# {ghost Object o}  */ {
    public void  f(int a) /*# requires o */
    {
	this.a=a;
    }
    public int a /*# guarded_by o */;
}



class C {
    Object x;
    D/*#{this.x}*/ dd;
    void f() {
	//dd.a = 2;
	dd.f(2);
	synchronized(this.x) {
	    //   dd.a = 2;
         dd.f(2);
	}
    }
}
