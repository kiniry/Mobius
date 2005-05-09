/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.prover;

/**
 * An object of this class represent a "result" produced by Simplify.
 * 
 * @see Simplify
 * @see escjava.prover.CECEnum
 * @see SExp
 */

public class SimplifyResult extends SimplifyOutput
{
    /*@ spec_public @*/ SList labels;
    /*@ spec_public @*/ SList context;

    //@ normal_behavior
    //@   ensures \result == labels;
    public /*@ pure @*/ SList getLabels() {
        return labels;
    }

    //@ normal_behavior
    //@   ensures \result == context;
    public /*@ pure @*/ SList getContext() {
        return context;
    }

    //@ normal_behavior  
    //@   requires COUNTEREXAMPLE <= kind && kind < END;
    //-@   modifies this.*;
    //@   ensures this.kind == kind;
    //@   ensures this.labels == labels;
    //@   ensures this.context == context;
    SimplifyResult(int kind, SList labels, SList context) {
        super(kind);
        this.labels = labels;
        this.context = context;
    }

    public /*@ pure non_null @*/ String toString() {
        return super.toString() + " labels=" + labels + " context=" + context;
    }
}
