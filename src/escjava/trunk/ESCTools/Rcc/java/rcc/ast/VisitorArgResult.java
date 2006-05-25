/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;


import java.util.Hashtable;

import javafe.ast.*;

import javafe.ast.Expr;
import rcc.ast.Visitor;      // Work around 1.0.2 compiler bug
import rcc.ast.VisitorArgResult;      // Work around 1.0.2 compiler bug
import rcc.ast.TagConstants; // Work around 1.0.2 compiler bug
import rcc.ast.GeneratedTags;// Work around 1.0.2 compiler bug
import rcc.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor
//# VisitorARRoot javafe.ast.VisitorArgResult

public abstract class VisitorArgResult extends javafe.ast.VisitorArgResult {
  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitAnOverview(AnOverview x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitHoldsStmtPragma(HoldsStmtPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitRequiresModifierPragma(RequiresModifierPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitGuardedByModifierPragma(GuardedByModifierPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitThreadLocalStatusPragma(ThreadLocalStatusPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitReadOnlyModifierPragma(ReadOnlyModifierPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitArrayGuardModifierPragma(ArrayGuardModifierPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitNowarnPragma(NowarnPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitGenericArgumentPragma(GenericArgumentPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitGenericParameterPragma(GenericParameterPragma x, Object o);

  //@ requires x != null;
  //@ ensures \result != null;
  public abstract Object visitGhostDeclPragma(GhostDeclPragma x, Object o);

}
