// Tests the parsing of non_null in model declarations

class non_null {
}

public class NonNull {

	void q(/*@ non_null */ Object o);
/*@
	model void m(int i);
	model void m(non_null Object i);
	model void m(non_null i);

	model NonNull(int i);
	model NonNull(non_null Object i);
	model NonNull(non_null i);

	model void p() {
		Object o = null;
		m(o);
	}
	model void p2() {
		Object o = null;
		new NonNull(o);
	}
	model void p3() {
		new NonNull(new non_null());
		m(new non_null());
		m(5);
		new NonNull(5);
        }
	model void p4() {
		Object o = null;
		q(o);
	}
*/
	
	void r() {
		Object o = null;
		q(o);
	}

}

