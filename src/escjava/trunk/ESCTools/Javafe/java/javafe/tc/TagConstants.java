/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.tc;

public class TagConstants extends javafe.parser.TagConstants
{
    public static final int TYPESIG = javafe.parser.TagConstants.LAST_TAG + 1;

    public static final int LAST_TAG = TYPESIG;

    //@ ensures \result != null;
    public static String toString(int tag) {
	switch (tag) {
	    case TYPESIG:
		return "TYPESIG";

	    default:
		return javafe.parser.TagConstants.toString(tag);
	}
    }
} // end of class TagConstants

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 85
 * End:
 */
