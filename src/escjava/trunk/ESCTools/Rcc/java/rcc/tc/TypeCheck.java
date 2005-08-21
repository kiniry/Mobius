/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import javafe.ast.ModifierPragmaVec;
import rcc.ast.TagConstants;

import javafe.tc.TypeSig;
import javafe.util.Info;
import java.util.Enumeration;
import javafe.ast.*;
import javafe.util.Set;
import javafe.util.Assert;
import javafe.util.Info;

public class TypeCheck extends javafe.tc.TypeCheck {
    
    /**
     ** Creates a instance of TypeCheck, and sets the <code>inst</code>
     ** field to this instance. Only one instance should be created. 
     ** Also initializes PrepTypeDeclaration.
     **/
    public TypeCheck() {
	super();
	inst = this;
	new rcc.tc.PrepTypeDeclaration();
    }
    
    
    /**
     ** Called to obtain the algorithm for performing name resolution
     ** and type checking.  Returns an instance of
     ** <code>rcc.tc.FlowInsensitiveChecks</code>.
     **/
    public javafe.tc.FlowInsensitiveChecks makeFlowInsensitiveChecks() {
	return new rcc.tc.FlowInsensitiveChecks();
    }
    
    /**
     ** Can a member of type target with modifiers
     ** modifiers/pmodifiers be accessed by code located in from? <p>
     **
     ** Note: pmodifiers may be null. <p>
     **/
    public boolean canAccess(/*@ non_null @*/ TypeSig from, 
			     /*@ non_null @*/ TypeSig target,
			     int modifiers,
			     ModifierPragmaVec pmodifiers) {
	if (FlowInsensitiveChecks.inAnnotation) {
	    return true;
	}
	
	if (Modifiers.isPublic(modifiers))
	    return true;
	if (Modifiers.isProtected(modifiers) && from.isSubtypeOf(target))
	    return true;
	if (!Modifiers.isPrivate(modifiers))  // aka, protected, package
	    return from.inSamePackageAs(target);
	
	/*
	 * private case -- have same enclosing class? [1.1]:
	 */
	while (from.enclosingType!=null)
	    from = from.enclosingType;
	while (target.enclosingType!=null)
      	    target = target.enclosingType;
	return target==from;
    }
    
}



