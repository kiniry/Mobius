// Tests the behavior of non_null under inheritance
public class NL extends S {
	Object oo;
// CASE 2:
	// Parent has non_null
	// No spec, so inherit the full spec of the parent method
	public void m(Object o) {
		o = null;  // FAILS  // FIXME
	}
	// Parent has non_null
	// No spec, so inherit the full spec of the parent method
	public void m2(Object o) {
		nonnull(o); // OK
	}
	public void mm1() {
		m(oo);  // FAILS
	}
	public void mm2() {
		(new S()).m(oo);  // FAILS
	}
// CASE 1:
	// Parent has non_null
	//@ also
	//@ requires true;
	public void qm2(Object o) {
		nonnull(o); // FAILS 
	}
	// Parent has non_null
	//@ also
	//@ requires true;
	public void qm(Object o) {
		o = null;  // OK
	}
	public void qmm1() {
		qm(oo); // OK 
	}
	public void qmm2() {
		(new S()).qm(oo);   // FAILS
	}
// CASE 1b:
	// Parent has non_null
	//@ also
	//@ requires false;
	public void qqm2(Object o) {
		nonnull(o); // OK 
	}
	// Parent has non_null
	//@ also
	//@ requires false;
	public void qqm(Object o) {
		o = null;  // FAILS // FIXME
	}
	public void qqmm1() {
		qqm(oo); // FAILS 
	}
	public void qqmm2() {
		(new S()).qqm(oo);   // FAILS
	}
// CASE 3:
	// Parent is not non_null
	public void n2(/*@ non_null */ Object o) {
		nonnull(o); // FAILS
	}
	// Parent is not non_null
	public void n(/*@ non_null */ Object o) {
		o = null;  // OK   // FIXME
	}
	public void nn() {
		n(oo);  // OK
	}
	public void nn2() {
		(new S()).n(oo);  // OK
	}

	public void p(/*@ non_null */ Object o) {
		o = null;  // FAILS
	}
	public void p2(/*@ non_null */ Object o) {
		nonnull(o); // OK
	}
	public void pp() {
		p(oo);  // FAILS
	}
	public void pp2() {
		(new S()).p(oo); // FAILS 
	}

}

class S {
	public void nonnull(/*@ non_null */ Object o);

	public void m(/*@ non_null */ Object o) {
		o = null;  // FAILS
	}
	public void m2(/*@ non_null */ Object o) {
	}
	public void qm(/*@ non_null */ Object o) {
		o = null;  // FAILS
	}
	public void qm2(/*@ non_null */ Object o) {
	}
	public void qqm(/*@ non_null */ Object o) {
		o = null;  // FAILS
	}
	public void qqm2(/*@ non_null */ Object o) {
	}
	public void n(Object o) {
		o = null;  // OK
	}
	public void n2(Object o) {
		nonnull(o); // FAILS
	}
	public void p(/*@ non_null */ Object o) {
		o = null;  // FAILS
	}
	public void p2(/*@ non_null */ Object o) {
		nonnull(o); // OK
	}
}
