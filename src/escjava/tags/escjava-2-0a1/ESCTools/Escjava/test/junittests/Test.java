public class Test {

	public int f = 1;

	//@ public model int size;
	//@ public represents size = f + 1;
	public static int size$V(Test t);
	//@ axiom (\forall Test t; t != null; size$V(t) == t.f + 1);

	//@ requires f == 1;
	//@ ensures size$V(this) == 2;
	public void z() { }

	//@ requires f == 0;
	//@ ensures size$V(this) == 2;
	public void zz() { f = 1; }

	//@ requires f == 0;
	//@ ensures size$V(this) == 2;
	public void zzz() { f = 2; }


	//@ requires j != 0;
	//@ requires f >= 0;
	//@ modifies f;
	//@ ensures \result > 0;
	//@ ensures f > 0;
	public int p( int j) {
		if (j > 0) return j;
		j = -j;
		return j;
	}

	//@ requires i != 0;
	//@ requires f > 0;
	//@ requires size > 1;
	//@ modifies f;
	//@ ensures \result > 0;
	//@ ensures size > 0;
	//@ ensures size$V(this) > 1;
	public int m(int i) {
		int k = i;
		int z = p(k);
		// set size = sizeValue();
		return z;
	}
}

