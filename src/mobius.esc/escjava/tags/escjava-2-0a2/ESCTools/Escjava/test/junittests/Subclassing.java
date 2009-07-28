// Tests that the subclassing contract is parsed and ignored

public class Subclassing {

	public int j;

	/*@
		subclassing_contract
		accessible j;
		callable n();
		measured_by i;
	*/
	public void m(int i){}

	public void n() {}

}
