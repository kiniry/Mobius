

public class Nowarn {

	//@ non_null
	public Object o = new Object();

	//@ non_null //@ nowarn
	public Object oo = new Object();

	public void m() {
		o = null; //@ nowarn NonNull ;
		oo = null;
	}
}
