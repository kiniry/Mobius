public class Methods {

	//@ requires i > 0;
	//@ ensures \result == i;
	public int f(int i) {
		return i;
	}

	//@ requires f(j) > 0;
	//@ ensures f(5) == 5;
	public int m(int j) {
		return j;
	}
}
