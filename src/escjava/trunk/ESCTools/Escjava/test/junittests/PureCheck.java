public class PureCheck extends A implements B {

	//@ invariant m() + n() == 0;
	//@ constraint n() == \old(n());
	//@ axiom PureCheck.m() + PureCheck.nn() == 0;
	//@ public model int modeli;
	//@ public represents modeli <- m() + n();
	//@ public depends modeli <- oo[m()],oo[nn()];
	//@ invariant (new PureCheck()).k() + (new PureCheck(1)).k() > 0;
	//@ invariant (new PureCheck[5]).length > 0;

	public int j = m() + n();
	//@ public ghost int jj = m() + n();
	public Object[] oo;

	//@ ensures m() + mp() + n() + k() > 0;
	public PureCheck() {}

	//@ ensures true;
	//@ model pure int k() {}

	//@ requires true;
	//@ pure model static int m();
	//@ model static pure int mp();
	public static int nn();
	/*@ pure */
	public /*@ non_null */ static String mm();
	//@ pure
	public /*@ non_null */ static String mmm();

	//@ modifies j if m()+nn() == 0;
	//@ modifies oo[m()+nn()];
	//@ requires mm().length() + nn() > 0;
	//@ requires m() + mp() + n() + k() > 0;
	//@ when m() + n() > 0;
	//@ signals (Exception e) m() + n() > 0;
	//@ duration m() + n();
	//@ working_space m() + n();
	//@ measured_by m() + n();
	//@ diverges m() + n() > 0;
	// accessible oo[m()+n()];  // FIXME
	public int p();

	// This one is at the end just to check that we can use before
	// declaring.
	//@ model int n();

	//@ helper
	private
	/*@ pure */ static void q() {}

	public //@ pure
	static void qq();

	//@ non_null pure helper
	private String ss() {}

	//@ ensures kk(p());
	public /*@ pure */ PureCheck(int i) {}

	//@ ensures true;
	//@ pure
	public boolean kk(int i) { return true; }

	int am();
	int aq();
	public int an();
	public int ap();

	//@ invariant am() + ap() + an() + aq() == 0;
}

class A extends D implements C {
	//@ pure
	int am();

	int aq();

}

interface B {
	//@ pure
	int an();
}

interface C {
	//@ pure
	int ap();
}

class D {
	//@ pure 
	int aq();
}
