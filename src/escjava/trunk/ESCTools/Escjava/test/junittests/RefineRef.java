public class RefineRef {

	//@ requires r != null;
	public void m(RefineRefHelper r) {
		r.o.getClass();
	}
	//@ requires r != null;
	public void mm(RefineRefHelper r) {
		r.oo.getClass();
	}
	//@ requires r != null;
	public void mmm(RefineRefHelper r) {
		r.ooo.getClass();
	}
}
