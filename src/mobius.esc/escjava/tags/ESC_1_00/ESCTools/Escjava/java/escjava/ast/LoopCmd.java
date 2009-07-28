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



public class LoopCmd extends GuardedCmd {
  public int locStart;

  public int locEnd;

  public int locHotspot;

  public /*@non_null*/ Hashtable oldmap;

  public /*@non_null*/ ConditionVec invariants;

  public /*@non_null*/ DecreasesInfoVec decreases;

  public /*@non_null*/ LocalVarDeclVec skolemConstants;

  public /*@non_null*/ ExprVec predicates;

  public /*@non_null*/ GenericVarDeclVec tempVars;

  public /*@non_null*/ GuardedCmd guard;

  public /*@non_null*/ GuardedCmd body;


  public GuardedCmd desugared;
  
  public int getStartLoc() { return locStart; }
  public int getEndLoc() { return locEnd; }


// Generated boilerplate constructors:

  /**
   ** Construct a raw LoopCmd whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected LoopCmd() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.invariants != null) sz += this.invariants.size();
     if (this.decreases != null) sz += this.decreases.size();
     if (this.skolemConstants != null) sz += this.skolemConstants.size();
     if (this.predicates != null) sz += this.predicates.size();
     if (this.tempVars != null) sz += this.tempVars.size();
     return sz + 3;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.oldmap;
     else index--;

     sz = (this.invariants == null ? 0 : this.invariants.size());
     if (0 <= index && index < sz)
        return this.invariants.elementAt(index);
     else index -= sz;

     sz = (this.decreases == null ? 0 : this.decreases.size());
     if (0 <= index && index < sz)
        return this.decreases.elementAt(index);
     else index -= sz;

     sz = (this.skolemConstants == null ? 0 : this.skolemConstants.size());
     if (0 <= index && index < sz)
        return this.skolemConstants.elementAt(index);
     else index -= sz;

     sz = (this.predicates == null ? 0 : this.predicates.size());
     if (0 <= index && index < sz)
        return this.predicates.elementAt(index);
     else index -= sz;

     sz = (this.tempVars == null ? 0 : this.tempVars.size());
     if (0 <= index && index < sz)
        return this.tempVars.elementAt(index);
     else index -= sz;

     if (index == 0) return this.guard;
     else index--;

     if (index == 0) return this.body;
     else index--;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[LoopCmd"
        + " locStart = " + this.locStart
        + " locEnd = " + this.locEnd
        + " locHotspot = " + this.locHotspot
        + " oldmap = " + this.oldmap
        + " invariants = " + this.invariants
        + " decreases = " + this.decreases
        + " skolemConstants = " + this.skolemConstants
        + " predicates = " + this.predicates
        + " tempVars = " + this.tempVars
        + " guard = " + this.guard
        + " body = " + this.body
        + "]";
  }

  public final int getTag() {
     return TagConstants.LOOPCMD;
  }

  public final void accept(javafe.ast.Visitor v) { 
    if (v instanceof Visitor) ((Visitor)v).visitLoopCmd(this);
  }

  public final Object accept(javafe.ast.VisitorArgResult v, Object o) { 
    if (v instanceof VisitorArgResult) return ((VisitorArgResult)v).visitLoopCmd(this, o); else return null;
  }

  public void check() {
     super.check();
     if (this.oldmap == null) throw new RuntimeException();
     for(int i = 0; i < this.invariants.size(); i++)
        this.invariants.elementAt(i).check();
     for(int i = 0; i < this.decreases.size(); i++)
        this.decreases.elementAt(i).check();
     for(int i = 0; i < this.skolemConstants.size(); i++)
        this.skolemConstants.elementAt(i).check();
     for(int i = 0; i < this.predicates.size(); i++)
        this.predicates.elementAt(i).check();
     for(int i = 0; i < this.tempVars.size(); i++)
        this.tempVars.elementAt(i).check();
     this.guard.check();
     this.body.check();
  }

  //@ ensures \result!=null
  public static LoopCmd make(int locStart, int locEnd, int locHotspot, /*@non_null*/ Hashtable oldmap, /*@non_null*/ ConditionVec invariants, /*@non_null*/ DecreasesInfoVec decreases, /*@non_null*/ LocalVarDeclVec skolemConstants, /*@non_null*/ ExprVec predicates, /*@non_null*/ GenericVarDeclVec tempVars, /*@non_null*/ GuardedCmd guard, /*@non_null*/ GuardedCmd body) {
     //@ set I_will_establish_invariants_afterwards = true
     LoopCmd result = new LoopCmd();
     result.locStart = locStart;
     result.locEnd = locEnd;
     result.locHotspot = locHotspot;
     result.oldmap = oldmap;
     result.invariants = invariants;
     result.decreases = decreases;
     result.skolemConstants = skolemConstants;
     result.predicates = predicates;
     result.tempVars = tempVars;
     result.guard = guard;
     result.body = body;
     return result;
  }
}
