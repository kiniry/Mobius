//@ pure
public class ModifiesPure {

	public int i;

	//@ modifies i;
	public void m();

	//@ public normal_behavior
        //@ {|
	//@	assignable i;
	//@ also
	//@	assignable \nothing;
        //@ |}
	public void n();
}


class ModifiesPureA {

	public int i;

	//@ modifies i;
	//@ pure
	public void m();

	//@ public normal_behavior
        //@ {|
	//@	assignable i;
	//@ also
	//@	assignable \nothing;
        //@ |}
	public /*@ pure @*/ void n();
}
