// This test checks whether we get warnings because of misuse of 'also'

public class AlsoInherit extends Parent {

	//@ ensures true;
	public void m();

	//@ ensures true;
	public void n();

	//@ also
	//@ ensures true;
	public void malso();

	//@ also
	//@ ensures true;
	public void nalso();

	//@ also_ensures true;
	public void p();

	//@ also_ensures true;
	public void pp();

}

class Parent {
	//@ ensures true;
	public void m();

	//@ also
	//@ ensures true;
	public void malso();

	//@ ensures true;
	public void p();
}
