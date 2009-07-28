//@ pure
public class ParsePure {

	//@ pure model int m() {}
	//@ public pure model int m1() {}
	//@ pure public model int m2() {}
	//@ pure model public int m3() {}

	//@ model pure int n();
	//@ public model pure int n1();
	//@ model public pure int n2();
	//@ model pure public int n3();

	//@ pure
	public ParsePure() {}

	//@ pure
	public void p() {}

	public /*@ pure */ void q();
}

class A extends B implements C,E {

	public void a() {}
	public void b() {}
	public void c() {}
	public void d() {}
}

class B extends D {
	//@ pure
	public void c() {}
}

//@ pure
class D {
	public void d() {}
}

interface C {

	//@ pure
	public void a();

}

//@ pure
interface E {
	public void b();
}
