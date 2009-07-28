/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;


import java.util.Hashtable;

import javafe.ast.*;
import escjava.ast.Visitor;      // Work around 1.0.2 compiler bug
import escjava.ast.TagConstants; // Work around 1.0.2 compiler bug
import escjava.ast.GeneratedTags;// Work around 1.0.2 compiler bug
import escjava.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor



public class SeqCmd extends GuardedCmd {
  // denotes g1 ; g2 ; ... ; gn
  public /*@non_null*/ GuardedCmdVec cmds;


  private void postCheck() {
    Assert.notFalse(1 < cmds.size());
  }

  public int getStartLoc() { return cmds.elementAt(0).getStartLoc(); }
  public int getEndLoc() { return cmds.elementAt(cmds.size()-1).getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw SeqCmd whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected SeqCmd() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.cmds != null) sz += this.cmds.size();
     return sz + 0;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     sz = (this.cmds == null ? 0 : this.cmds.size());
     if (0 <= index && index < sz)
        return this.cmds.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[SeqCmd"
        + " cmds = " + this.cmds
        + "]";
  }

  public final int getTag() {
     return TagConstants.SEQCMD;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitSeqCmd(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitSeqCmd(this, o); else return null;
  }

  public void check() {
     super.check();
     for(int i = 0; i < this.cmds.size(); i++)
        this.cmds.elementAt(i).check();
     postCheck();
  }

  //@ ensures \result!=null
  public static SeqCmd make(/*@non_null*/ GuardedCmdVec cmds) {
     //@ set I_will_establish_invariants_afterwards = true
     SeqCmd result = new SeqCmd();
     result.cmds = cmds;
     return result;
  }
}
