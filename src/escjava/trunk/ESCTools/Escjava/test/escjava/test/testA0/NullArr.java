/**
 * Test the new semantics of non-null arrays.
 *
 * This test show the results of an intermediate implementation of the feature
 * under which non_null applied to an array type constrains all array
 * component types to be non_null.
 *
 * Once the feature is fully implemented, then it will be necessary to add
 * non_null at the point indicated by !non_null.
 */
public class NullArr {
    public /*@non_null*/ Object m(/*@non_null*/ Object /*!non_null*/ [] a) {
	if(a.length > 1)
	    return a[0];
	else
	    return "";
    }
}
