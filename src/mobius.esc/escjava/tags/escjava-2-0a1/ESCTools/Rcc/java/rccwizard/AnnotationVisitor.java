/* Copyright 2000, 2001, Compaq Computer Corporation */

// Copyright (c) 1999, Compaq Computer Corporation
// Authors:  Cormac Flanagan and Rustan Leino.

package rccwizard;

import java.util.*;

import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;
import rcc.ast.*;

public class AnnotationVisitor extends DefaultVisitor {
    
    /*@ non_null */ Hashtable envBase;
    
    public void visitTypeDecl(TypeDecl x) {
	envBase = new Hashtable();
	if (Main.guessnull) {
	    envBase.put("null", Types.javaLangObject());
	}

	Annotator modifierAnnotator = new Annotator("<L", x.locId, x.id.toString(), "type decl", "");
	if( !Main.readonly ) {
	    modifierAnnotator.put("thread_local");
	}
	super.visitTypeDecl(x);
    }

    private boolean isObjectArrayType(Type t) {
	if (!(t instanceof ArrayType)) {
	    return false;
	}
	return Types.isReferenceType(((ArrayType)t).elemType);
    }
    
    public void visitRoutineDecl(RoutineDecl rd) {
	int kind;
	String ms;
	Identifier routineName;

	// hack to make public methods have no requires clauses:
	// we put this in to check AWT where we didn't have the whole program.
	if (Main.pmnr && Modifiers.isPublic(rd.modifiers)) return;

	if (! (rd instanceof MethodDecl)) {
	    ms = "constructor";
	    kind = 0;
	    //@ assume rd.parent != null;
	    routineName = rd.parent.id;
	    if (rd.implicit) return;
	} else {
	    MethodDecl md = (MethodDecl)rd;
	    routineName = md.id;
	    if (Modifiers.isStatic(md.modifiers)) {
		ms = "static method";
		kind = 1;
		if (md.id.toString().equals("main") && md.args.size() == 1) {
		    GenericVarDecl decl = rd.args.elementAt(0);
		    if (isObjectArrayType(decl.type)) {
			// main routine, special annotation guesses
			if( !Main.readonly && Main.guessnull) {
			    Annotator requiresAnnotator = 
				new Annotator(rd, "parameter:" + ms, 
					      "requires ");
			    requiresAnnotator.put("null");
			}
			return;
		    }
		}
	    } else if (! (md.parent instanceof ClassDecl)) {
		ms = "interface method";
		kind = 2;
	    } else if (TypeCheck.inst.getAllOverrides(md).isEmpty()) {
		ms = "instance method";
		kind = 2;
	    } else if (TypeCheck.inst.getOverrides(md)==null) {
		ms = "interface method override";
		kind = 3;
	    } else {
		ms = "class method override";
		kind = 4;
	    }
	}

	Annotator requiresAnnotator = 
	    new Annotator(rd, "parameter:" + ms, "requires ");


	
	boolean isStatic=Modifiers.isStatic(rd.modifiers) ||
	    rd instanceof ConstructorDecl;
	//@ assume rd.parent != null;
	Hashtable envReq = getEnv( rd.parent,
				   !isStatic,
				   accessLevel(rd.modifiers),
				   true,
				   false,
				   null );
	
	for(int i = 0; i < rd.args.size(); i++) {
	    GenericVarDecl decl = rd.args.elementAt(i);
	    // Remove any field named arg; it is not in scope
	    try {
		envReq.remove( decl.id.toString() );
	    } catch( NullPointerException ex ) {
	    }
	}
	
	for( Enumeration e = envReq.keys(); e.hasMoreElements(); ) {
	    String expr2 = (String)e.nextElement();
	    Type type2 = (Type)envReq.get(expr2);
	    
	    if (Types.isReferenceType(type2) && !Main.readonly) {
		requiresAnnotator.put(expr2);
	    }
	}
    }
    
    public void visitFieldDecl(FieldDecl fd) {
	String kind = Modifiers.isStatic(fd.modifiers) ? "static field" : "instance field";
	String name = fd.id.toString();
	Annotator modifierAnnotator = new Annotator("<<", fd.locId, name, kind, "");
	
        if (Modifiers.isFinal(fd.modifiers)) {
	    return;
        }

	if( Main.readonly ) {
	    modifierAnnotator.put("readonly");
	}
	
	//@ assume fd.parent != null;
	Hashtable env = getEnv( fd.parent, 
				!Modifiers.isStatic( fd.modifiers),
				0,
				!isConstantFinal(fd),
				false,
				null );


	for( Enumeration e = env.keys(); e.hasMoreElements(); ) {
	    String expr2 = (String)e.nextElement();
	    Type type2 = (Type)env.get(expr2);
	    
	    if (Types.isReferenceType(type2) && !Main.readonly) {
		modifierAnnotator.put("guarded_by "+expr2);
	    }
	}
    }
    
    //@ ensures RES != null;
    //@ ensures RES.keyType == type(String);
    //@ ensures RES.elementType == type(Type);
    private Hashtable getEnv(/*@ non_null */ TypeDecl td,
			     boolean allowInstance,
			     int accessLevel,
			     boolean allowConstantFinals,
			     boolean returnNonConstantNames,
			     FieldDecl fdUpto) {
	Hashtable env = (Hashtable)envBase.clone();
	
	//@ assume env.keyType == type(String);
	//@ assume env.elementType == type(Type);
	
	TypeSig sig = TypeSig.getSig( td );
	FieldDeclVec fds = sig.getFields();

	if (allowInstance) { 
	    env.put("this", sig);
	} else {
	    env.put(td.id + ".class", Types.javaLangObject());
	}
	
	for(int i=0; i<fds.size(); i++) {
	    FieldDecl fd = fds.elementAt(i);
	    //@ assume fd.parent != null;
	    
	    // Consider adding fd to env
	    
	    if( fd == fdUpto ) {
		return env;
	    }
	    
	    if( !returnNonConstantNames 
		&& !Modifiers.isFinal( fd.modifiers )
		&& readOnlyPragma( fd.pmodifiers ) == null) {
		continue;
	    }

	    if( !allowInstance && !Modifiers.isStatic( fd.modifiers ))
		// Dont include instance field
		continue;
	    
	    if(	accessLevel( fd.modifiers ) < accessLevel)
		// Field is more private than the reference to it would be
		continue;
	    
	    TypeSig fdsig = TypeSig.getSig( fd.parent );
	    if( !TypeCheck.inst.canAccess( sig, fdsig, fd.modifiers, fd.pmodifiers ))
		// Cannot access the field
		continue;
	    
	    if (!allowConstantFinals && isConstantFinal(fd)) {
		continue;
	    }
	    
	    
	    // Ok, add field to env
	    env.put( fd.id.toString(), fd.type );
	    
	}
	
	return env;
    }
    
    private boolean isConstantFinal(FieldDecl fd) {
	return Modifiers.isFinal(fd.modifiers) &&
	    fd.init != null &&
	    fd.init instanceof Expr &&
	    ConstantExpr.eval( (Expr)fd.init ) != null;
    }
    
    
    /** Returns an integer corresponding to the access modifiers in
	"modifiers". */
    
    private int accessLevel(int modifiers) {
	// TBW:  also check for spec_public
	if( Modifiers.isPrivate(modifiers)) return 0;
	if( Modifiers.isProtected(modifiers)) return 2;
	if( Modifiers.isPublic(modifiers)) return 3;
	return 1;
    }

    private ReadOnlyModifierPragma readOnlyPragma(ModifierPragmaVec m) {
	if (m==null) return null;
	for (int i = 0; i<m.size(); i++) {
	    if (m.elementAt(i) instanceof ReadOnlyModifierPragma) {
		return (ReadOnlyModifierPragma)m.elementAt(i);
	    }
	}
	return null;
    }
    
}

