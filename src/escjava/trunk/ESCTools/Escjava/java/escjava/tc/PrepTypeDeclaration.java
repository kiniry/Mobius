package escjava.tc;

import javafe.ast.TypeDeclElem;
import javafe.tc.TypeSig;
import javafe.ast.FieldDecl;
import javafe.ast.MethodDecl;
import javafe.util.ErrorSet;
import escjava.ast.GhostDeclPragma;
import escjava.ast.ModelDeclPragma;
import escjava.ast.ModelMethodDeclPragma;
import escjava.ast.ModelConstructorDeclPragma;
import escjava.ast.ModelTypePragma;
import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.ast.Utils;

public class PrepTypeDeclaration extends javafe.tc.PrepTypeDeclaration {

    public PrepTypeDeclaration() {
	inst = this;
    }


    protected void visitTypeDeclElem(/*@non_null*/ TypeDeclElem e,
				 /*@non_null*/ TypeSig currentSig,
				 boolean abstractMethodsOK,
				 boolean inFinalClass,
				 boolean inInterface ) {
	if (e instanceof GhostDeclPragma) {
	    GhostDeclPragma g = (GhostDeclPragma)e;
	    FieldDecl x = g.decl;

	    if (Modifiers.isStatic(x.modifiers) && !inInterface
		&& !currentSig.isTopLevelType() && !Modifiers.isFinal(x.modifiers))
		ErrorSet.error(x.locId,
		  "Inner classes may not declare static members, unless they" +
		  " are compile-time constant fields");

	    // ghost fields differ from regular fields in that transient and
	    // volatile do not apply to them
	    checkModifiers( x.modifiers,
		(inInterface ? Modifiers.ACC_PUBLIC : Modifiers.ACCESS_MODIFIERS)
				 | Modifiers.ACC_FINAL | Modifiers.ACC_STATIC ,
		x.locId, inInterface ? "ghost interface field" : "ghost field");

	    // ghost fields in an interface are implicitly public
	    // they are not implicitly final as Java fields are
	    // they are implicitly static only if they are not declared instance
	    if (inInterface) {
		x.modifiers |= Modifiers.ACC_PUBLIC;
		if (Utils.findModifierPragma(
			x.pmodifiers, TagConstants.INSTANCE) == null) {
		    x.modifiers |= Modifiers.ACC_STATIC;
		}
	    }

	    // FIXME - Java fields check for duplicate type names here
	    // where is this done for ghost fields; also I don't think there
	    // is a check anywhere that a ghost field is hiding a 
	    // super class Java field (or enclosing class Java field)

	    getEnvForCurrentSig(currentSig, true).resolveType( currentSig, x.type);

	} else if (e instanceof ModelDeclPragma) {
	    FieldDecl x = ((ModelDeclPragma)e).decl;

	    if (Modifiers.isStatic(x.modifiers) && !inInterface
		&& !currentSig.isTopLevelType() && !Modifiers.isFinal(x.modifiers))
		ErrorSet.error(x.locId,
		  "Inner classes may not declare static members, unless they" +
		  " are compile-time constant fields");

	    // model fields differ from regular fields in that transient and
	    // volatile do not apply to them
	    checkModifiers( x.modifiers,
		(inInterface ? Modifiers.ACC_PUBLIC : Modifiers.ACCESS_MODIFIERS)
				 | Modifiers.ACC_FINAL | Modifiers.ACC_STATIC ,
		x.locId, inInterface ? "model interface field" : "model field");

	    // model fields in an interface are implicitly public
	    // they are not implicitly final as Java fields are
	    // they are implicitly static only if they are not declared instance
	    if (inInterface) {
		x.modifiers |= Modifiers.ACC_PUBLIC;
		if (Utils.findModifierPragma(
			x.pmodifiers, TagConstants.INSTANCE) == null) {
		    x.modifiers |= Modifiers.ACC_STATIC;
		}
	    }

	    // FIXME - Java fields check for duplicate type names here
	    // where is this done for ghost fields; also I don't think there
	    // is a check anywhere that a ghost field is hiding a 
	    // super class Java field (or enclosing class Java field)

	    getEnvForCurrentSig(currentSig, true).resolveType( currentSig, x.type);

/*
	These are not needed at present because routines and types are 
	converted into regular Java routines and types prior to any
	type prepping or type checking.  However, this causes some scope
	problems.  When those are fixed, we may need to prep these types
	here in a manner similar to that done in javafe.tc.PrepTypeDeclaration

	} else if (e instanceof ModelMethodDeclPragma) {
	    ModelMethodDeclPragma g = (ModelMethodDeclPragma)e;
	    MethodDecl x = g.decl;

	    if (Modifiers.isStatic(x.modifiers) && !inInterface 
		&& !currentSig.isTopLevelType())
		ErrorSet.error(x.locId,
			"Only methods of top-level classes may be static");

	    if (inInterface)
		checkModifiers( x.modifiers, 
			Modifiers.ACC_PUBLIC | Modifiers.ACC_ABSTRACT,
			x.loc, "model interface method");
	    else
		checkModifiers( x.modifiers, Modifiers.ACCESS_MODIFIERS |
			Modifiers.ACC_ABSTRACT | Modifiers.ACC_FINAL |
			Modifiers.ACC_SYNCHRONIZED | Modifiers.ACC_STATIC |
			Modifiers.ACC_STRICT,
			x.loc, "model method");
		// Model methods may not be native

	    if (inInterface)
		x.modifiers |= Modifiers.ACC_ABSTRACT | Modifiers.ACC_PUBLIC;

	    if (Modifiers.isPrivate(x.modifiers) || inFinalClass)
		x.modifiers |= Modifiers.ACC_FINAL;

	    if (Modifiers.isAbstract(x.modifiers) &&
		(Modifiers.isPrivate(x.modifiers) |
		 Modifiers.isStatic(x.modifiers)  |
		 Modifiers.isFinal(x.modifiers)  |
		 Modifiers.isNative(x.modifiers)  |
		 Modifiers.isSynchronized(x.modifiers)) )
		ErrorSet.error (x.locId,
		    "Incompatible modifiers for an abstract method");

		// FIXME - resolve types
		// FIXME - check for duplicate method ids
		System.out.println("MODEL METHOD PRAGMA");
		
	} else if (e instanceof ModelConstructorDeclPragma) {
		// FIXME - stuff from non-model constructor
		System.out.println("MODEL CONSTRUCTOR PRAGMA");
	} else if (e instanceof ModelTypePragma) {
		System.out.println("MODEL TYPE PRAGMA");
*/
	} else 
	    super.visitTypeDeclElem(e,currentSig,abstractMethodsOK, 
			inFinalClass, inInterface);
    }

}
