/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;


import java.util.Hashtable;

import javafe.ast.*;
// import escjava.ast.Visitor;      // Work around 1.0.2 compiler bug
// import escjava.ast.TagConstants; // Work around 1.0.2 compiler bug
// import escjava.ast.GeneratedTags;// Work around 1.0.2 compiler bug
// import escjava.ast.AnOverview;   // Work around 1.0.2 compiler bug
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor


public interface GeneratedTags {
   int SUBSTEXPR = javafe.tc.TagConstants.LAST_TAG + 1;
   int TYPEEXPR = SUBSTEXPR + 1;
   int LABELEXPR = TYPEEXPR + 1;
   int WILDREFEXPR = LABELEXPR + 1;
   int GUARDEXPR = WILDREFEXPR + 1;
   int RESEXPR = GUARDEXPR + 1;
   int LOCKSETEXPR = RESEXPR + 1;
   int DEFPREDLETEXPR = LOCKSETEXPR + 1;
   int DEFPREDAPPLEXPR = DEFPREDLETEXPR + 1;
   int GETSCMD = DEFPREDAPPLEXPR + 1;
   int SUBGETSCMD = GETSCMD + 1;
   int SUBSUBGETSCMD = SUBGETSCMD + 1;
   int RESTOREFROMCMD = SUBSUBGETSCMD + 1;
   int VARINCMD = RESTOREFROMCMD + 1;
   int DYNINSTCMD = VARINCMD + 1;
   int SEQCMD = DYNINSTCMD + 1;
   int LOOPCMD = SEQCMD + 1;
   int CALL = LOOPCMD + 1;
   int GHOSTDECLPRAGMA = CALL + 1;
   int STILLDEFERREDDECLPRAGMA = GHOSTDECLPRAGMA + 1;
   int SETSTMTPRAGMA = STILLDEFERREDDECLPRAGMA + 1;
   int SKOLEMCONSTANTPRAGMA = SETSTMTPRAGMA + 1;
   int NOWARNPRAGMA = SKOLEMCONSTANTPRAGMA + 1;
   int SPEC = NOWARNPRAGMA + 1;
   int CONDITION = SPEC + 1;
   int DEFPRED = CONDITION + 1;
   int LAST_TAG = DEFPRED;
}
