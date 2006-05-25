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

public class GeneratedTags extends javafe.tc.TagConstants {
   static public final int HOLDSSTMTPRAGMA = javafe.tc.TagConstants.LAST_TAG + 1;
   static public final int REQUIRESMODIFIERPRAGMA = HOLDSSTMTPRAGMA + 1;
   static public final int GUARDEDBYMODIFIERPRAGMA = REQUIRESMODIFIERPRAGMA + 1;
   static public final int THREADLOCALSTATUSPRAGMA = GUARDEDBYMODIFIERPRAGMA + 1;
   static public final int READONLYMODIFIERPRAGMA = THREADLOCALSTATUSPRAGMA + 1;
   static public final int ARRAYGUARDMODIFIERPRAGMA = READONLYMODIFIERPRAGMA + 1;
   static public final int NOWARNPRAGMA = ARRAYGUARDMODIFIERPRAGMA + 1;
   static public final int GENERICARGUMENTPRAGMA = NOWARNPRAGMA + 1;
   static public final int GENERICPARAMETERPRAGMA = GENERICARGUMENTPRAGMA + 1;
   static public final int GHOSTDECLPRAGMA = GENERICPARAMETERPRAGMA + 1;
   static public final int LAST_TAG = GHOSTDECLPRAGMA;


    static public /*@ non_null @*/ String toString(int tag) {
      switch (tag) {
        case HOLDSSTMTPRAGMA: return "HOLDSSTMTPRAGMA";
        case REQUIRESMODIFIERPRAGMA: return "REQUIRESMODIFIERPRAGMA";
        case GUARDEDBYMODIFIERPRAGMA: return "GUARDEDBYMODIFIERPRAGMA";
        case THREADLOCALSTATUSPRAGMA: return "THREADLOCALSTATUSPRAGMA";
        case READONLYMODIFIERPRAGMA: return "READONLYMODIFIERPRAGMA";
        case ARRAYGUARDMODIFIERPRAGMA: return "ARRAYGUARDMODIFIERPRAGMA";
        case NOWARNPRAGMA: return "NOWARNPRAGMA";
        case GENERICARGUMENTPRAGMA: return "GENERICARGUMENTPRAGMA";
        case GENERICPARAMETERPRAGMA: return "GENERICPARAMETERPRAGMA";
        case GHOSTDECLPRAGMA: return "GHOSTDECLPRAGMA";
        default: return javafe.tc.TagConstants.toString(tag); 
      }
    }
}
