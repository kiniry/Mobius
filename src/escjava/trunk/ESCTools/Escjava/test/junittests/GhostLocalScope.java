public class GhostLocalScope {

	//@ ghost public int i;
	public int ii;
	public Object z;

	public void m() {

		//@ set i = 0;
		int kk = 0;
		/*@ non_null */ Object o = null;
		//@ ghost non_null Object ooo;
		//@ non_null ghost Object o4;
		//@ final non_null ghost Object o5;
		//@ ghost int k = 9;
		//@ set i = 1;
		//@ set k = kk;
		//@ set k = i;
		//@ set kk = 8; // ERROR
		kk = 9;
		kk = i; // ERROR
		kk = k; // ERROR
		kk = ii;

		//@ ghost int z;
		Object op = z; // OK - should be the field z

		Object y;
		//@ ghost Object y; // ERROR - Duplicate

	}

	static public void mm() {
		int kk = 0;
		kk = ii; // ERROR
		kk = i;  // ERROR
		//@ ghost int k = 0;
		//@ set k = i; // ERROR
		//@ set k = ii; // ERROR
		//@ set k = kk; // OK
		kk = k; // ERROR
	}
}
