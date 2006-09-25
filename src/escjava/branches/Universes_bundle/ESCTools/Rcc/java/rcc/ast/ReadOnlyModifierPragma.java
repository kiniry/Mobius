/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.ast.ModifierPragma;

// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

// # TagBase javafe.tc.TagConstants.LAST_TAG + 1
// # VisitorRoot javafe.ast.Visitor
// # VisitorARRoot javafe.ast.VisitorArgResult

public class ReadOnlyModifierPragma extends ModifierPragma {
    public int loc;

    public int getStartLoc() {
        return loc;
    }

    // Generated boilerplate constructors:

    // @ ensures this.loc == loc;
    protected ReadOnlyModifierPragma(int loc) {
        this.loc = loc;
    }

    // Generated boilerplate methods:

    public final int childCount() {
        return 0;
    }

    public final Object childAt(int index) {
        /* throws IndexOutOfBoundsException */
        if (index < 0)
            throw new IndexOutOfBoundsException("AST child index " + index);
        int indexPre = index;

        throw new IndexOutOfBoundsException("AST child index " + indexPre);
    } // @ nowarn Exception;

    public final/* @non_null */String toString() {
        return "[ReadOnlyModifierPragma" + " loc = " + this.loc + "]";
    }

    public final int getTag() {
        return TagConstants.READONLYMODIFIERPRAGMA;
    }

    public final void accept(javafe.ast.Visitor v) {
        if (v instanceof Visitor)
            ((Visitor) v).visitReadOnlyModifierPragma(this);
    }

    public final Object accept(javafe.ast.VisitorArgResult v, Object o) {
        if (v instanceof VisitorArgResult)
            return ((VisitorArgResult) v).visitReadOnlyModifierPragma(this, o);
        else
            return null;
    }

    public void check() { /* do nothing */}

    // @ ensures \result != null;
    public static ReadOnlyModifierPragma make(int loc) {
        ReadOnlyModifierPragma result = new ReadOnlyModifierPragma(loc);
        return result;
    }
}
