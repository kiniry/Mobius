/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;


import java.io.*;

import java.util.Enumeration;
import java.util.Hashtable;


import javafe.ast.*;
import javafe.util.Location;
import javafe.util.Assert;

import rcc.ast.TagConstants;


public class RccPrettyPrint extends DelegatingPrettyPrint {
    public RccPrettyPrint() { }
    
    public RccPrettyPrint(PrettyPrint self, PrettyPrint del) {
	super(self, del);
    }
    
    public void print(OutputStream o, LexicalPragma lp) {
	if (lp.getTag() == TagConstants.NOWARNPRAGMA) {
	    write(o, "//# nowarn");
	    NowarnPragma nwp = (NowarnPragma)lp;
	    for (int i = 0; i < nwp.checks.size(); i++) {
		if (i == 0) write(o, ' ');
		else write(o, ", ");
		write(o, nwp.checks.elementAt(i).toString());
	    }
	    write(o, '\n');
	} else writeln(o, "// Unknown LexicalPragma (tag = " + lp.getTag() + ')');
    }
    
    
    public void print(OutputStream o, int ind, TypeModifierPragma mp) {
	int tag = mp.getTag();
	switch (tag) {
	    
	case TagConstants.ARRAYGUARDMODIFIERPRAGMA:{
	    ArrayGuardModifierPragma vemp = (ArrayGuardModifierPragma)mp;
	    write(o, "/*# elems_guarded_by "); 
	    printnp(o, ind, vemp.expressions); write(o, "  */");
	    break;
	}	
	default:
	    write(o, "/* Unknown TypeModifierPragma (tag = " + tag + ")"); write(o, "  */");
	    break;
	}
    }

public void print(OutputStream o, int ind, ModifierPragma mp) {
	int tag = mp.getTag();
	switch (tag) {
	    
	case TagConstants.REQUIRESMODIFIERPRAGMA:{
	    RequiresModifierPragma vemp = (RequiresModifierPragma)mp;
	    write(o, "/*# requires "); 
	    printnp(o, ind, vemp.expressions); write(o, "  */");
	    break;
	}
	case TagConstants.GUARDEDBYMODIFIERPRAGMA: {
	    GuardedByModifierPragma vemp = (GuardedByModifierPragma)mp;
	    write(o, "/*# guarded_by ");
	    printnp(o, ind, vemp.expressions); write(o, "  */");
	    break;
	}
	case TagConstants.THREADLOCALSTATUSPRAGMA: { 
	    ThreadLocalStatusPragma p = (ThreadLocalStatusPragma)mp;
	    if (p.local) {
		write(o, "/*# thread_local */");
	    } else {
		write(o, "/*# thread_shared */");
	    }
	    break;
	}
	
	default:
	    write(o, "/* Unknown ModifierPragma (tag = " + tag + ")"); write(o, "  */");
	    break;
	}
    }
    
    
    public void printnp(OutputStream o, int ind, ExprVec es) {
	if (es == null) write(o, "<null ExprVec>");
	else {
	    for (int i = 0; i < es.size(); i++) {
		if (i!=0) write(o, ", ");
		self.print(o, ind, es.elementAt(i));
	    }

	}
    }
    
    public void print(OutputStream o, int ind, StmtPragma sp) {
	int tag = sp.getTag();
	switch (tag) {
	    
	case TagConstants.HOLDSSTMTPRAGMA: {
	    ExprVec expressions = ((HoldsStmtPragma)sp).expressions;
	    write(o, "/*# holds ");
	    printnp(o, ind, expressions);
	    write(o, "  */");
	    break;
	}
	
	
	default:
	    write(o, "/* Unknown StmtPragma (tag = " + tag + ")"); write(o, "  */");
	    break;
	}
    }

 public final String toString( TypeModifierPragmaVec mp) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    for (int i = 0; i < mp.size(); i++) {
	self.print(result, 0, mp.elementAt(i));
    }
    return result.toString();
  }


}
