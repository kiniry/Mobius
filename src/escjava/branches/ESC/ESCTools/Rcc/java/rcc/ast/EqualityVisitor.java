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

public class EqualityVisitor  extends javafe.ast.EqualityVisitor {
   //@ ensures RES!=null
   public Object visitAnOverview(AnOverview y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitHoldsStmtPragma(HoldsStmtPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof HoldsStmtPragma)) return new Boolean(false);
      boolean x = true;  
      HoldsStmtPragma z = (HoldsStmtPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitRequiresModifierPragma(RequiresModifierPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof RequiresModifierPragma)) return new Boolean(false);
      boolean x = true;  
      RequiresModifierPragma z = (RequiresModifierPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitGuardedByModifierPragma(GuardedByModifierPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof GuardedByModifierPragma)) return new Boolean(false);
      boolean x = true;  
      GuardedByModifierPragma z = (GuardedByModifierPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitThreadLocalStatusPragma(ThreadLocalStatusPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ThreadLocalStatusPragma)) return new Boolean(false);
      boolean x = true;  
      ThreadLocalStatusPragma z = (ThreadLocalStatusPragma)o;
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitReadOnlyModifierPragma(ReadOnlyModifierPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ReadOnlyModifierPragma)) return new Boolean(false);
      boolean x = true;  
      ReadOnlyModifierPragma z = (ReadOnlyModifierPragma)o;
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitArrayGuardModifierPragma(ArrayGuardModifierPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ArrayGuardModifierPragma)) return new Boolean(false);
      boolean x = true;  
      ArrayGuardModifierPragma z = (ArrayGuardModifierPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitNowarnPragma(NowarnPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof NowarnPragma)) return new Boolean(false);
      boolean x = true;  
      NowarnPragma z = (NowarnPragma)o;
      x = x && (z.checks == y.checks);
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitGenericArgumentPragma(GenericArgumentPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof GenericArgumentPragma)) return new Boolean(false);
      boolean x = true;  
      GenericArgumentPragma z = (GenericArgumentPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitGenericParameterPragma(GenericParameterPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof GenericParameterPragma)) return new Boolean(false);
      boolean x = true;  
      GenericParameterPragma z = (GenericParameterPragma)o;
      if (!(y.args == null && z.args == null)) {
         if (y.args != null && z.args != null && (z.args.size() == y.args.size())) {
            for (int i = 0; i < z.args.size(); i++) {
               x = x && ((Boolean)z.args.elementAt(i).accept(this, y.args.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitGhostDeclPragma(GhostDeclPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof GhostDeclPragma)) return new Boolean(false);
      boolean x = true;  
      GhostDeclPragma z = (GhostDeclPragma)o;
      x = x && (y.decl == null && z.decl == null ||  (y.decl != null && z.decl != null && ((Boolean)(y.decl.accept(this, z.decl))).booleanValue()));
      return new Boolean(x);
   }

}
