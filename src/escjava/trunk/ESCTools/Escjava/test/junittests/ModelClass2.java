public class Model {

/*@
    public model class M {
	public int i;
	public non_null Object o = new Object();
	invariant i > 0;  nowarn ;
	protected invariant i > 0;

	requires i > 1;
	also
	ensures true;
	protected void m();


	{|
		requires true;
	also
		ensures true;
	|}
	pure
	public void n();

	public ghost int j;
	public model float f;
	public invariant j == 0;
    }
*/


}

/* FIXME
- nowarn on line 7 seems to turn off warnings on line 8 as well
- need to turn on the MODIFIERPRAGMAS and connect with declaration
- nothing with the POST modifier pragmas
- and what is the 4th kind of pragma?
- what about method, field, constructor keywords
*/
