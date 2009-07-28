// Tests the problem case of non_null on formal arguments with inheritance

public class NonNullBad extends NonNullBadS implements NonNullBadI {

	public void m(/*@ non_null */ Object o,
			Object oo,
			/*@ non_null */ Object ooo);

	//@ non_null
	public void mm();

	//@ non_null
	public int mmm();

	public void mmmm(/*@ non_null */ int i);
}

class NonNullBadS {

	public void m(/*@ non_null */ Object o, /*@ non_null */ Object oo, Object ooo);

}

interface NonNullBadI extends NonNullBadII {
	public void m(/*@ non_null */ Object o, /*@ non_null */ Object oo, /*@ non_null */ Object ooo);

}

interface NonNullBadII {
	public void m(Object o, /*@ non_null */ Object oo, /*@ non_null */ Object ooo);

}
