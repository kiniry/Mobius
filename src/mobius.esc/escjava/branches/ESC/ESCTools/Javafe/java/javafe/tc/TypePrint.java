/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.tc;


import javafe.ast.*;
import javafe.tc.TagConstants; // Work around compiler bug
import java.io.OutputStream;


public class TypePrint extends DelegatingPrettyPrint {

  // Caller must establish del!=null!
  //@ requires false
  public TypePrint() { }

  //@ requires self!=null && del!=null
  public TypePrint(PrettyPrint self, PrettyPrint del) {
    super(self, del);
  }


  public void print(OutputStream o, int ind, VarInit e) {
    if (e instanceof Expr) {
      Type t = FlowInsensitiveChecks.getTypeOrNull((Expr)e);

      write(o, "(/*");
      if (t==null)
	write(o, "UNAVAILABLE");
      else
        write(o, Types.printName(t));
      write(o, "*/ ");

      del.print(o, ind, e);
      write(o, ')');
    } else del.print(o, ind, e);
  }
}
