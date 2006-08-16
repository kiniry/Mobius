/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.ast.IdentifierVec;
import javafe.ast.LexicalPragma;

// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

// # TagBase javafe.tc.TagConstants.LAST_TAG + 1
// # VisitorRoot javafe.ast.Visitor
// # VisitorARRoot javafe.ast.VisitorArgResult

public class NowarnPragma extends LexicalPragma {
    public/* @ non_null @ */IdentifierVec checks;

    public int loc;

    boolean triggered = false;

    public int getStartLoc() {
        return loc;
    }

    // Generated boilerplate constructors:

    // @ ensures this.checks == checks;
    // @ ensures this.loc == loc;
    protected NowarnPragma(/* @ non_null @ */IdentifierVec checks, int loc) {
        this.checks = checks;
        this.loc = loc;
    }

    // Generated boilerplate methods:

    public final int childCount() {
        int sz = 0;
        if (this.checks != null) sz += this.checks.size();
        return sz + 0;
    }

    public final Object childAt(int index) {
        /* throws IndexOutOfBoundsException */
        if (index < 0)
            throw new IndexOutOfBoundsException("AST child index " + index);
        int indexPre = index;

        int sz;

        sz = (this.checks == null ? 0 : this.checks.size());
        if (0 <= index && index < sz)
            return this.checks.elementAt(index);
        else
            index -= sz;

        throw new IndexOutOfBoundsException("AST child index " + indexPre);
    } // @ nowarn Exception;

    public final/* @non_null */String toString() {
        return "[NowarnPragma" + " checks = " + this.checks + " loc = "
            + this.loc + "]";
    }

    public final int getTag() {
        return TagConstants.NOWARNPRAGMA;
    }

    public final void accept(javafe.ast.Visitor v) {
        if (v instanceof Visitor) ((Visitor) v).visitNowarnPragma(this);
    }

    public final Object accept(javafe.ast.VisitorArgResult v, Object o) {
        if (v instanceof VisitorArgResult)
            return ((VisitorArgResult) v).visitNowarnPragma(this, o);
        else
            return null;
    }

    public void check() {
        if (this.checks == null) throw new RuntimeException();
    }

    // @ ensures \result != null;
    public static NowarnPragma make(
        /* @ non_null @ */IdentifierVec checks,
        int loc) {
        NowarnPragma result = new NowarnPragma(checks, loc);
        return result;
    }
}
