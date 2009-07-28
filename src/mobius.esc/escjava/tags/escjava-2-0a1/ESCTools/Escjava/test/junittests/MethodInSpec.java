public class MethodInSpec {

	//@ ensures \result == true;
	public boolean m();

	//@ requires i >= 0;
	//@ ensures \result == (i==0);
	//@ pure
	public boolean m(int i);


	//@ requires i>0 && this.m(i);
	public void n(int i);
}
