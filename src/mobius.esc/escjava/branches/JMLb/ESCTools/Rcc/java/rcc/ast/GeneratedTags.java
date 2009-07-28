/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;


import java.util.Hashtable;

import javafe.ast.*;

import javafe.ast.Expr;
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor
//# VisitorARRoot javafe.ast.VisitorArgResult

public interface GeneratedTags {
   int HOLDSSTMTPRAGMA = javafe.tc.TagConstants.LAST_TAG + 1;
   int REQUIRESMODIFIERPRAGMA = HOLDSSTMTPRAGMA + 1;
   int GUARDEDBYMODIFIERPRAGMA = REQUIRESMODIFIERPRAGMA + 1;
   int THREADLOCALSTATUSPRAGMA = GUARDEDBYMODIFIERPRAGMA + 1;
   int READONLYMODIFIERPRAGMA = THREADLOCALSTATUSPRAGMA + 1;
   int ARRAYGUARDMODIFIERPRAGMA = READONLYMODIFIERPRAGMA + 1;
   int NOWARNPRAGMA = ARRAYGUARDMODIFIERPRAGMA + 1;
   int GENERICARGUMENTPRAGMA = NOWARNPRAGMA + 1;
   int GENERICPARAMETERPRAGMA = GENERICARGUMENTPRAGMA + 1;
   int GHOSTDECLPRAGMA = GENERICPARAMETERPRAGMA + 1;
   int LAST_TAG = GHOSTDECLPRAGMA;
}
