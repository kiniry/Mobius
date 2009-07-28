// Tests the informal predicate

public class Informal {

	public int i;

	//@ ensures (* ok *);
	//@ ensures ! (* ok *);
	//@ modifies (* stuff *), i;
	//@ signals (Exception e) (* ok *);
	public void m() {}

}
