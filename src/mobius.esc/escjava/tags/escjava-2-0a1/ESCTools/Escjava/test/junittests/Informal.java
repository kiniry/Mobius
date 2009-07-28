// Tests the informal predicate

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
	// subclassing_contract
	//	measured_by (* ok *);
	//	callable (* ok *);
	//	accessible (* ok *);
	public void m() {}

}
