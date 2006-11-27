/**
 * Test case for a field of type Objec[];
 */
public class NullArr1b {
    private /*@non_null*/ Object /*!non_null*/ [] a = new Object[0];
    public /*@non_null*/ Object m() {
	if(a.length > 1)
	    return a[0]; // ok under new semantics.
	else
	    return "";
    }
}
