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

//# EndHeader

/**
	
	The files in this package extend the AST classes defined in
	<code>javafe.ast</code>.  The following diagram shows how the new
	classes related to the old classes in the class hierarchy:
	
	* <PRE>
	* - ASTNode
	*    - Stmt ()
	*       - StmtPragma ()
	*         + HoldStmtPragma (Expr* locks) 
	*    - ModifierPragma ()
	*         + RequiresPragma (Expr* locks) 
	*         + GuardedByPragma (Expr* locks)
	*         + ThreadLocalStatusPragma (boolean local) 
	*         + ReadOnlyPragma (boolean local) 
	*    - LexicalPragma ()
	*      + NowarnPragma (Identifier* checks)
	*    - TypeModifierPragma ()
	*      + ArrayGuardModifierPragma (Expr* locks)
	* </PRE>
	
	(Classes with a <code>-</code> next to them are defined in
	<code>javafe.ast</code>; classes with a <code>+</code> are defined in
	this package.
	
	(P.S. Ignore the stuff that appears below; the only purpose of this class
	is to contain the above overview.)
	
	@see javafe.ast.AnOverview
	
	*/

public abstract class AnOverview extends ASTNode {
}

public class HoldsStmtPragma extends StmtPragma {
	//# Expr* expressions
  //# int loc
			
	public int getStartLoc() { return loc; }
	public int getEndLoc() { return expressions.elementAt(expressions.size()-1).getEndLoc(); }
}

public class RequiresModifierPragma extends ModifierPragma {
	//# Expr* expressions
  //# int loc
			
	public int getStartLoc() { return loc; }
	public int getEndLoc() { 
		if (expressions.size() ==0)
	    return super.getEndLoc();
		Expr e=expressions.elementAt(expressions.size()-1);
		return e.getEndLoc();
	}
}


public class GuardedByModifierPragma extends ModifierPragma {
	//# Expr* expressions
  //# int loc
			
	public int getStartLoc() { return loc; }
	public int getEndLoc() { 
		if (expressions.size()==0)
	    return super.getEndLoc();
		
		Expr e=expressions.elementAt(expressions.size()-1);
		return e.getEndLoc();
	}
}

public class ThreadLocalStatusPragma extends ModifierPragma {
	//# boolean local
  //# int loc
			
	public int getStartLoc() { return loc; }
}

public class ReadOnlyModifierPragma extends ModifierPragma {
  //# int loc
			
	public int getStartLoc() { return loc; }
}

public class ArrayGuardModifierPragma extends TypeModifierPragma {
	//# Expr* expressions
  //# int loc
			
	public int getStartLoc() { return loc; }
	public int getEndLoc() { 
		if (expressions.size()==0)
	    return super.getEndLoc();
		
		Expr e=expressions.elementAt(expressions.size()-1);
		return e.getEndLoc();
	}
}


public class NowarnPragma extends LexicalPragma {
	//# Identifier* checks NoCheck
        //# int loc
	boolean triggered = false;

	public int getStartLoc() { return loc; }
}


public class GenericArgumentPragma extends TypeModifierPragma {
	//# Expr* expressions
  //# int loc
			
	public int getStartLoc() { return loc; }
	public int getEndLoc() { 
		if (expressions.size()==0)
	    return super.getEndLoc();
		
		Expr e=expressions.elementAt(expressions.size()-1);
		return e.getEndLoc();
	}
}



public class GenericParameterPragma extends TypeModifierPragma {
	//# FormalParaDecl* args
  //# int loc
			
	public int getStartLoc() { return loc; }
	public int getEndLoc() { 
		if (args.size()==0)
	    return super.getEndLoc();
		
		FormalParaDecl e= args.elementAt(args.size()-1);
		return e.getEndLoc();
	}
}



public class GhostDeclPragma extends TypeDeclElemPragma {
  //# FieldDecl decl
  //# int loc

  public void setParent(TypeDecl p) {
    super.setParent(p);
    if (decl!=null)
	decl.setParent(p);
  }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { return decl.getEndLoc(); }
}
