public class ParseWhen {

	public boolean b,bb;

	//@ requires b;
	//@ when bb;
	public void m();

	//@ requires bb;
	//@ measured_by b if bb;
	public void n();
}
