// Tests that specifications that are after the declaration are read
//#FLAGS: -checkPurity
public class After {

	native public boolean m()
		//@ requires true;
		//@ ensures false;
	;

	native public boolean purem()
		//@ pure
		//@ requires true;
		//@ ensures false;
	;

	public int n()
		//@ pure
		/*@ requires true;
		    ensures false;
		    ensures purem() && m();
		*/
	{
	}
}
