/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;

import javafe.ast.Expr;
import javafe.ast.VariableAccess;
import javafe.util.Location;
import javafe.util.Assert;


public class DecreasesInfo {
  // the location of the 'decreases' pragma
  public final int loc;
  //@ invariant loc != Location.NULL;

  // the translated expression
  public final /*@ non_null */ Expr f;

  // a local variable storing the previous value of expr "f"
  public final /*@ non_null */ VariableAccess fOld;

  //@ requires loc != Location.NULL;
  public DecreasesInfo(int loc, /*@ non_null */ Expr f,
		       /*@ non_null */ VariableAccess fOld) {
    this.loc = loc;
    this.f = f;
    this.fOld = fOld;
  }

  public void check() {
    Assert.notFalse(loc != Location.NULL &&
		    f != null && fOld != null);
  }
}
