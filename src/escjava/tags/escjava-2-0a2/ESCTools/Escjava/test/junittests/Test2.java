public class Test2 {

	public static int size$V(int i);
	public static int f = 10;

	//@ axiom (\forall int i;; size$V(i) == i + 1);

	//@ requires f == 10;
	//@ modifies f;
	//@ ensures size$V(f) == 21;
	public void m() {
		f = f+10;
	}
}
