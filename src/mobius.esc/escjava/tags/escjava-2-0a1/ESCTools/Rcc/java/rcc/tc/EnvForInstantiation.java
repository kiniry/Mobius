/* Copyright 2000, 2001, Compaq Computer Corporation */


package rcc.tc;

import rcc.ast.*;
import rcc.ast.TagConstants;
import javafe.tc.*;
import javafe.util.*;
import javafe.ast.*;

/**
 ** EnvForInstantiation are used to build environment during Prep
 ** that is used when typechecking type parameters.
 **/

public class EnvForInstantiation extends GhostEnv {
    
    boolean reallyStatic;
    FieldDeclVec fields;
    MethodDeclVec methods;
    // ConstructorDeclVec constructors; /* this may not be needed */

    // THIS IS A HACK.  I'M SURE IT WILL BREAK LOTS OF THINGS.
    public boolean isStaticContext() {
	return false;
    }
    
    public  EnvForInstantiation(/*@non_null*/ Env parent,
				/*@non_null*/ javafe.tc.TypeSig peer,
				FieldDeclVec fields,
				MethodDeclVec methods,
				boolean staticContext) {
	super(parent, peer, staticContext);
	this.fields = fields;
	this.methods = methods;
	reallyStatic = staticContext;
	//this.constructors = constructors;
    }
    
    /**
     ** Display information about an Env to System.out.  This function
     ** is intended only for debugging use.
     **/
    public void display() {
	parent.display();
	System.out.println("[[ extended with the partially created typesig for "
			   + peer.getExternalName() + " ]]");
    }
    
    
    public javafe.tc.TypeSig lookupSimpleTypeName(Identifier id, int loc) {
	// Check for a definition in peer:
	javafe.tc.TypeSig result = peer.lookupType(id, loc);
	if (result!=null)
	    return result;
	
	// Otherwise, look to enclosing scopes...
	return parent.lookupSimpleTypeName(id, loc);
    }
    
    
    /** This is to allow overriding by subclasses **/
    
    protected boolean hasField(Identifier id) {

      for (int i = 0; i <  fields.size(); i++) {
	    FieldDecl fd =  fields.elementAt(i);
	    if (fd.id == id)
		return true;
	}

	
	if (!FlowInsensitiveChecks.inAnnotation)
	    return false;
	
	return (getGhostField(id.toString(), null) != null);
    }
    
    
    protected boolean hasMethod(Identifier id) {
	for (int i = 0; i < methods.size(); i++) {
	    MethodDecl md = methods.elementAt(i);
	    if (md.id == id)
		return true;
	}
	
	return false;
    }
    
}
