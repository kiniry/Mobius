// Tests the informal predicate
// FIXME - add the remaining predicates
public class Informal {

	public int i;

	//@ requires (* ok *);
	//@ diverges (* ok *);
	//@ ensures (* ok *);
	//@ ensures ! (* ok *);
	//@ modifies (* stuff *), i;
	//@ signals (Exception e) (* ok *);
	//@ when (* ok *);
	//@ duration (* ok *) ? 0:0;
	//@ working_space (* ok *)?0:0;
	// accessible (* ok *);
	//	measured_by (* ok *);
	//	callable (* ok *);
	public void m() {}

}
