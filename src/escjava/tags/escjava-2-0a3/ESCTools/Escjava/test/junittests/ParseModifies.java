public class ParseModifies {

	public boolean b,bb,bbb;

	//@ modifies b;
	public void m();

	//@ requires b;
	//@ modifies bbb;
	//@ also
	//@ requires bb;
	//@ modifies b;
	public void mm();

	public boolean r,rr,r2;
	//@ requires r;
	//@ requires r2;
	//@ modifies b if bbb, bb if b;
	//@ also requires rr;
	//@ modifies b if true, bb if false;
	public void q();

	public int i,j;
	//@ ensures j == i;
	public void z() {
		i = i+1;
	}
}
