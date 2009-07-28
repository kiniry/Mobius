/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.filespace;

/**
 ** The exceptional result type for lookup:
 **/

public class Resolve_AmbiguousName extends Exception {

    Tree ambiguousPackage;	// The package that is also a reference type

    public Resolve_AmbiguousName(String message, Tree P) {
	super(message);
	ambiguousPackage = P;
    }
}
