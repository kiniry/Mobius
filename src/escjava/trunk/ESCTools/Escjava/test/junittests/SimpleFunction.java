public class SimpleFunction {

	//-@ function
	/*@ pure */ public static int bump(int i);
	public static int f = 10;
	public int j = 50;

	//@ axiom (\forall int i;; bump(i) == i + 1);

	//@ requires f >= 10;
	//@ requires j >= 50;
	//@ modifies f,j;
	//@ ensures bump(f) >= 21;
	//@ ensures bump(j) >= 61;
	public void m() {
		f = f+10;
		j = j + 10;
	}

	//@ ensures bump(f+j) < 10;
	public void n() {} // FAILS
}
