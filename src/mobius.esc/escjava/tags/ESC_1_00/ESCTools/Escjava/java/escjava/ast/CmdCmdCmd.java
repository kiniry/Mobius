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


 

public class CmdCmdCmd extends GuardedCmd {
  // denotes g1 ! g2  or  g1 [] g2
  public int cmd;

  public /*@non_null*/ GuardedCmd g1;

  public /*@non_null*/ GuardedCmd g2;


  public final int getTag() { return cmd; }

  private void postCheck() {
    boolean goodtag =
      (cmd == TagConstants.TRYCMD || cmd == TagConstants.CHOOSECMD);
    Assert.notFalse(goodtag);
  }

  public int getStartLoc() { return g1.getStartLoc(); }
  public int getEndLoc() { return g2.getEndLoc(); }


// Generated boilerplate constructors:

  /**
   ** Construct a raw CmdCmdCmd whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected CmdCmdCmd() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     return 2;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.g1;
     else index--;

     if (index == 0) return this.g2;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[CmdCmdCmd"
        + " cmd = " + this.cmd
        + " g1 = " + this.g1
        + " g2 = " + this.g2
        + "]";
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitCmdCmdCmd(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitCmdCmdCmd(this, o); else return null;
  }

  public void check() {
     super.check();
     this.g1.check();
     this.g2.check();
     postCheck();
  }

  //@ ensures \result!=null
  public static CmdCmdCmd make(int cmd, /*@non_null*/ GuardedCmd g1, /*@non_null*/ GuardedCmd g2) {
     //@ set I_will_establish_invariants_afterwards = true
     CmdCmdCmd result = new CmdCmdCmd();
     result.cmd = cmd;
     result.g1 = g1;
     result.g2 = g2;
     return result;
  }
}
