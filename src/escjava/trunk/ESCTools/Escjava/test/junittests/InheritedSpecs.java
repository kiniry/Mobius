


public class InheritedSpecs extends ISHelper {

	//@ also
	//@ requires i != 0;
	//@ ensures \result != 0;
	public int m(int i) {
		return i;
	}

	public void mm1() { m(0); }
	public void mm2() { m(-1); }
	public void mm3() { m(1); }
	public void mm4() { (new ISHelper()).m(0); }

}

class ISHelper {

	//@ requires i >= 0;
	//@ ensures \result >= 0;
	public int m(int i) { return 1; }
}


