/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/** Represents a try-catch statement.
 */

public class TryCatchStmt extends Stmt {
  public /*@non_null*/ Stmt tryClause;

  public /*@non_null*/ CatchClauseVec catchClauses;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;


  private void postCheck() {
    int t = tryClause.getTag();
    Assert.notFalse(t != TagConstants.SWITCHLABEL	//@ nowarn Pre
		    && t != TagConstants.CONSTRUCTORINVOCATION
		    && t != TagConstants.VARDECLSTMT);
  }
  public int getStartLoc() { return loc; }
  public int getEndLoc() { 
    if (catchClauses==null || catchClauses.size()<1)
      return tryClause.getEndLoc();

    return catchClauses.elementAt(catchClauses.size()-1).getEndLoc();
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw TryCatchStmt whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected TryCatchStmt() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.catchClauses != null) sz += this.catchClauses.size();
     return sz + 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.tryClause;
     else index--;

     sz = (this.catchClauses == null ? 0 : this.catchClauses.size());
     if (0 <= index && index < sz)
        return this.catchClauses.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[TryCatchStmt"
        + " tryClause = " + this.tryClause
        + " catchClauses = " + this.catchClauses
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.TRYCATCHSTMT;
  }

  public final void accept(Visitor v) { v.visitTryCatchStmt(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitTryCatchStmt(this, o); }

  public void check() {
     super.check();
     this.tryClause.check();
     for(int i = 0; i < this.catchClauses.size(); i++)
        this.catchClauses.elementAt(i).check();
     postCheck();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static TryCatchStmt make(/*@non_null*/ Stmt tryClause, /*@non_null*/ CatchClauseVec catchClauses, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     TryCatchStmt result = new TryCatchStmt();
     result.tryClause = tryClause;
     result.catchClauses = catchClauses;
     result.loc = loc;
     return result;
  }
}
