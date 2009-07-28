/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import rcc.tc.Instantiation;
import rcc.ast.TagConstants;
import rcc.ast.GenericArgumentPragma;
import rcc.ast.GenericParameterPragma;
import rcc.ast.*;
import rcc.parser.*;
import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;
import java.util.Hashtable;
import java.util.Vector;


public class PrepTypeDeclaration extends javafe.tc.PrepTypeDeclaration {
    
    public PrepTypeDeclaration() {
	inst = this;
    } //@ nowarn Invariant


    // rewrite this to not clone on every iteration.
    public void addClassGuardsToFields(TypeDecl d) {
	// add class guards

	if (d.pmodifiers == null) return;


	// clone because pragmas may be shared between fields, ie  Foo f,g,h;
	CloneAST clone = new CloneAST();
	for(int i = 0, sz = d.elems.size(); i < sz; i++) {
	    TypeDeclElem e = d.elems.elementAt(i);
	    if (e instanceof FieldDecl) {
		FieldDecl fd = (FieldDecl)e;
		ModifierPragma t[] = fd.pmodifiers.toArray();
		for (int j = 0; j < t.length; j++) {
		    t[j] = (ModifierPragma)clone.clone(t[j], true);
		}
		fd.pmodifiers = ModifierPragmaVec.make(t);
	    }
	}
		
	for (int j = 0; j < d.pmodifiers.size(); j++) {
	    ModifierPragma p = d.pmodifiers.elementAt(j);
	    if (p.getTag()==TagConstants.GUARDEDBYMODIFIERPRAGMA) {
		for(int i = 0, sz = d.elems.size(); i < sz; i++) {
		    TypeDeclElem e = d.elems.elementAt(i);
		    if (e instanceof FieldDecl) {
			FieldDecl fd = (FieldDecl)e;
			if ( !Modifiers.isFinal(fd.modifiers)) {
			    fd.pmodifiers.addElement(p);
			}
		    }
		}
	    }
	}
    }
    
    
    public boolean hasParameters(javafe.tc.TypeSig sig) {
	if (typeParametersDecoration.get(sig) != null) {
	    return true;
	}
	
	// look for type parameters
	TypeModifierPragmaVec v = sig.getTypeDecl().tmodifiers;
	if( v != null ) {
	    for( int i=0; i<v.size(); i++) {
		if (v.elementAt(i).getTag() == TagConstants.GENERICPARAMETERPRAGMA) {
		    return true;
		
		}
	    }
	}
	return false;
    }

    public void prepGenericTypeDecl(TypeSig s) {
	TypeDecl decl = s.getTypeDecl();
      
	checkTypeModifiers(decl, s, true);
	checkTypeModifierPragmaVec(decl.tmodifiers,
				       decl,
				       getEnvForCurrentSig(s, true),
				       s);
    }

				    
    
    
    //@ requires decl!=null && currentSig!=null
    public void visitClassDecl(ClassDecl decl,
			       javafe.tc.TypeSig currentSig ) {
	

      // Check that the modifiers are ok


	/*try 
	  {
	    throw new Exception("boo");
	  } catch (Exception e) {
	    e.printStackTrace();
	    } 
	*/

	if (!hasParameters(currentSig)) addClassGuardsToFields(decl);
	checkTypeModifiers(decl, currentSig, true);
	checkTypeModifierPragmaVec(decl.tmodifiers, decl,  getEnvForCurrentSig(currentSig, true), currentSig);

	// Visit all enclosed member declarations
	// They will add themselves to fieldSeq and methodSeq
	
	for(int i=0; i< decl.elems.size(); i++)
	    visitTypeDeclElem(decl.elems.elementAt(i),
			      currentSig,
			      Modifiers.isAbstract(decl.modifiers),
			      Modifiers.isFinal(decl.modifiers),
			      false );
	
     // Add members of direct superclass, if any
     // superclass may be null, or may name an interface
	
	TypeName superClassName = decl.superClass;
	javafe.tc.TypeSig superClassSig 
	    = superClassName == null ? null : TypeSig.getSig( superClassName );
	
	if( superClassSig != null ) {
	    if( superClassSig.getTypeDecl() instanceof ClassDecl ) 
		{	
		    // check superclass is not final
		    if( Modifiers.isFinal(superClassSig.getTypeDecl().modifiers) )
			ErrorSet.error(superClassName.getStartLoc(),
				       "Can't subclass final classes: class "
				       + superClassSig.getExternalName());
		    else
			addInheritedMembers( currentSig, superClassSig );
		    checkSuperTypeAccessible(currentSig, superClassSig,
					     superClassName==null ?
					     decl.getStartLoc() :
					     superClassName.getStartLoc());
		}
	    else
		{
		    ErrorSet.error( superClassName.getStartLoc(),
				    "Can't subclass interfaces: interface "
				    + superClassSig.getExternalName());
		}
	}
	
	// Add members of direct super interfaces
	
	checkSuperInterfaces( currentSig, decl.superInterfaces );
	
	// Check no two abstract methods with same method signature
	// and different return types
	
	for( int i=0; i<methodSeq.size(); i++ ) 
	    {
		MethodDecl mdi = (MethodDecl)methodSeq.elementAt(i);
		for( int j=0; j<i; j++ ) 
		    {
			MethodDecl mdj = (MethodDecl)methodSeq.elementAt(j);
			
			// Check if mdi and mdj are abstract methods
			// with same signature and different return types
			
			if(   Modifiers.isAbstract(mdi.modifiers)
			      && Modifiers.isAbstract(mdj.modifiers)
			      && Types.isSameMethodSig( mdi, mdj )
			      && !Types.isSameType( mdi.returnType, mdj.returnType ) )
			    {
				ErrorSet.error( decl.loc,
						"Class "+decl.id
						+" contains two abstract methods"
						+" with same signature"
						+" but different return types");
			    }
		    }
	    }
				// All done
    }
    
    
    
    //@ requires decl!=null && currentSig!=null
    public void visitInterfaceDecl(InterfaceDecl decl,
				   javafe.tc.TypeSig currentSig ) {

	addClassGuardsToFields(decl);
	// Check that the modifiers are ok
	checkTypeModifiers(decl, currentSig, false);
	checkTypeModifierPragmaVec(decl.tmodifiers, decl,  getEnvForCurrentSig(currentSig, true), currentSig);
	
	// Visit all enclosed member declarations
	// They will add themselves to fieldSeq and methodSeq
	
	for(int i=0; i<decl.elems.size(); i++)
	    visitTypeDeclElem(decl.elems.elementAt(i),
			      currentSig,
			      true, false, true );
	
	checkSuperInterfaces( currentSig, decl.superInterfaces);
	
	// interfaces inherit members from java.lang.Object
	addInheritedMembers( currentSig, Types.javaLangObject() );
	
	// ### STILL NEED TO CHECK NO DUPLICATE METHOD SIGNATURES ???
	// All done
    }
    
    
    static public ASTDecoration typeParametersDecoration = new ASTDecoration("type parameters");
    static public ASTDecoration parameterDeclDecoration =  new ASTDecoration("decl for parameter");
    
    
    //@ requires env!=null
    protected void checkTypeModifierPragmaVec(TypeModifierPragmaVec v, 
						  ASTNode ctxt, 
						  Env env,
						  javafe.tc.TypeSig currentSig ) {
	if( v != null )
	    for( int i=0; i<v.size(); i++)
		checkTypeModifierPragma( v.elementAt(i), ctxt, env, currentSig );
    }
    
    
    //@ requires p!=null && env!=null
    protected void checkTypeModifierPragma(TypeModifierPragma p,
					       ASTNode ctxt,
					       Env env,
					       javafe.tc.TypeSig currentSig) {
	int tag = p.getTag();
	switch(tag) 
	    {
	    case TagConstants.GENERICPARAMETERPRAGMA:
		{
		    GenericParameterPragma pp = (GenericParameterPragma)p;
		    if (typeParametersDecoration.get(currentSig)!=null) {
			if (typeParametersDecoration.get(currentSig) != pp.args) {
			    ErrorSet.error(
				       ctxt.getStartLoc(),
				       "can only have one type parameter list  for class or interface declaration.");
			}
			return;
		    }
			    
		    typeParametersDecoration.set(currentSig, pp.args);
		    for (int i = 0; i<pp.args.size(); i++) {
			FormalParaDecl parameter = pp.args.elementAt(i);
			env.resolveType(parameter.type);
			FieldDecl decl
			  = FieldDecl.make(parameter.modifiers  | Modifiers.ACC_FINAL, 
					     parameter.pmodifiers,
					     parameter.id, parameter.type,
					     parameter.locId, null,
					     Location.NULL);
			decl.setParent((TypeDecl)ctxt);
			GhostDeclPragma pragma = GhostDeclPragma.
			    make(decl, parameter.locId);
			((TypeDecl)ctxt).elems.insertElementAt(pragma, 0);
			parameterDeclDecoration.set(parameter, decl);
		    }
		    break;
		}
	    default:
		Assert.fail("Unexpected tag " + tag);
	    }
    }
    
    
    
    
    static protected InstantiationVec instantiations = InstantiationVec.make();
    static protected EqualsAST equality = new EqualsAST();
    static public final ASTDecoration  typeArgumentDecoration = new ASTDecoration("type args");
    static Hashtable declsForInstantiations = new Hashtable();
    
    protected javafe.tc.TypeSig findInstantiation(javafe.tc.TypeSig sig, ExprVec expressions) {
	for (int i = 0; i < instantiations.size(); i++) {
	    Instantiation instantiation = instantiations.elementAt(i);
	    if (instantiation.sig==sig&&
		equality.equals(instantiation.expressions,expressions)) {
		return instantiation.instantiation;
	    }
	}
	return null;
    }
    
    protected void processGenericArgumentPragmas(Env env, TypeName tn) {
	ExprVec expressions  = (ExprVec)typeArgumentDecoration.get(tn);
	if (expressions != null) {
	    return;
	}
	if (tn.tmodifiers==null) {
	    return;
	}

	
	for (int i = 0; i<tn.tmodifiers.size(); i++) {
	    TypeModifierPragma p = tn.tmodifiers.elementAt(i);

	    int tag = p.getTag();
	    switch(tag) {
	    case TagConstants.ARRAYGUARDMODIFIERPRAGMA:
		//handle later
		break;
		
	    case TagConstants.GENERICARGUMENTPRAGMA:
		if (typeArgumentDecoration.get(tn)!=null) {
		    ErrorSet.error(tn.getStartLoc(),
				   "can only have one type argument list  for class or interface name.");
		}
		GenericArgumentPragma gp = (GenericArgumentPragma)p;
		/*		
		javafe.tc.TypeSig sigForEnclosingClass = env.getEnclosingClass();
		FlowInsensitiveChecks fic =
		    new FlowInsensitiveChecks(sigForEnclosingClass,
					      getEnvForCurrentSig(sigForEnclosingClass, true));
		*/
		javafe.tc.TypeSig sigForEnclosingClass = env.getEnclosingClass();
		FlowInsensitiveChecks fic =
		    new FlowInsensitiveChecks(sigForEnclosingClass,
					      getEnvForCurrentSig(sigForEnclosingClass, false));
		boolean t = FlowInsensitiveChecks.inAnnotation;
		FlowInsensitiveChecks.inAnnotation = true;
	
		{
		    if (sigForEnclosingClass.state < TypeSig.PREPPED) {
			rcc.tc.TypeSig.prepPartDecoration.
			set(sigForEnclosingClass,
			    new PrepPart(getFieldsFromStack(),
				     getMethodsFromStack()));
		    }

		    // this is not quite right:  what if we are checking a static field: this should
		    // not be in context. 
			// fic.checkLockExprVec(getEnvForCurrentSig(sigForEnclosingClass, false), 
		    //		    System.out.println("env: ");
		    //env.display();
		    fic.checkLockExprVec(env, 
					 gp.expressions, Location.NULL);
		    rcc.tc.TypeSig.prepPartDecoration.
			set(sigForEnclosingClass, null);
		}

		FlowInsensitiveChecks.inAnnotation = t;
			
		typeArgumentDecoration.set(tn, gp.expressions);
		break;
	    default:
		
		Assert.fail("Unexpected tag " + tag);
	    }
	}
    }
    
    //@ ensures RES!=null
    public javafe.tc.TypeSig processTypeNameAnnotations(/*@non_null*/ TypeName tn, javafe.tc.TypeSig sig, Env env) {

	if (env.getEnclosingClass()==null) {
	    InterfaceDecl dummy = InterfaceDecl.make(0,null,
						     Identifier.intern("_dummy"),
						     TypeNameVec.make(),
						     null,
						     TypeDeclElemVec.make(),
						     Location.NULL,
						     Location.NULL,
						     Location.NULL,
						     Location.NULL);
	    env = new EnvForCU(sig.getCompilationUnit());
	    rcc.tc.TypeSig s = new rcc.tc.TypeSig(sig.packageName,
				    "_dummy",
				    sig,
				    dummy,
				    sig.getCompilationUnit());

       	    env = s.getEnclosingEnv();
	}
	
	processGenericArgumentPragmas(env, tn);
	ExprVec expressions = (ExprVec)typeArgumentDecoration.get(tn);
	return findTypeSignature(env, sig, expressions, tn.getStartLoc());
    }

	
    public javafe.tc.TypeSig findTypeSignature(Env env,
					       javafe.tc.TypeSig sig,
					       ExprVec expressions,
					       int locForError) {
	if (expressions==null) {
	    if (typeParametersDecoration.get(sig) != null) {
		ErrorSet.fatal(locForError,
			       "no " +
			       "type arguments given for " 
			       + sig.simpleName);	
	    } else {
		return sig;
	    }
	}

	javafe.tc.TypeSig instantiation = findInstantiation(sig, expressions);
	
	if (instantiation!=null) {
	    return instantiation;
	}
	return createInstantiation(env, sig, expressions);
    }
    
    protected   javafe.tc.TypeSig createInstantiation(Env env, javafe.tc.TypeSig sig, ExprVec expressions) {
	
	Info.out("[instantiating " + sig.simpleName + " with " + PrettyPrint.inst.toString(expressions) + "]");
	
	TypeDecl decl = sig.getTypeDecl();
	
	Assert.notNull(decl);

	// creates cycle sig.prep();  // make sure parameters are processed 

	TypeSig newSig = TypeSig.instantiate(sig, decl, expressions, env);
	
	FormalParaDeclVec parameters = (FormalParaDeclVec)PrepTypeDeclaration.
	    typeParametersDecoration.get(sig);
	if (parameters==null) {
	    checkTypeModifierPragmaVec(decl.tmodifiers,
					   decl,
					   getEnvForCurrentSig(sig, true),
					   sig);
	    parameters = (FormalParaDeclVec)PrepTypeDeclaration.
		typeParametersDecoration.get(sig);
	    if (parameters==null) {
		ErrorSet.fatal(decl.getStartLoc(),
			       "no " +
			       "type arguments expected for " 
			       + sig.simpleName);			   
	    }
	}
	if (expressions==null) {
	    ErrorSet.fatal(decl.getStartLoc(),
			   "no " +
			   "type arguments given for " 
			   + sig.simpleName);			   
	}
	if (parameters.size() != expressions.size()) {
	    ErrorSet.fatal(decl.getStartLoc(),
			   "mismatch in number of " +
			   "type arguments for " 
			   + sig.simpleName);			   
	}
	SubstitutionVec subs = SubstitutionVec.make();
	for (int i = 0; i<parameters.size(); i++) {
	    Expr expr = expressions.elementAt(i);
	    FormalParaDecl parameter =  parameters.elementAt(i);
	    
	    if (!javafe.tc.Types.
		isInvocationConvertable(FlowInsensitiveChecks.getType(expr),
					parameter.type)) {
		ErrorSet.error(expr.getStartLoc(),
			       "type of argument does not match parameter "+
			       "type "
			       + RccPrettyPrint.inst.
			       toString(parameter.type));
	    }
	    FieldAccess fa = FieldAccess.
		make(
		     ExprObjectDesignator.
		     make(parameter.getStartLoc(),
			  ThisExpr.make(sig,
					parameter.getStartLoc())),
		     parameter.id,
		     parameter.getStartLoc());
	    subs.addElement(new Substitution(fa, expr));
	    subs.addElement(new Substitution(AmbiguousVariableAccess.
					     make(
						  SimpleName.
						  make(parameter.id,
						       parameter.getStartLoc())),
					     expr));
	   
	}
	subs.addElement(new Substitution(
					 ThisExpr.
					 make(sig,
					      sig.getTypeDecl().getStartLoc()),
					 ThisExpr.
					 make(newSig,
					      sig.getTypeDecl().getStartLoc())));
	MultipleSubstitution ms =
	    new MultipleSubstitution(subs, new EqualsASTNoDecl());
	CloneWithSubstitution clone = new CloneForInstantiation(ms);
	decl = (TypeDecl)clone.clone(decl,true);
	newSig.finishInst(decl, (javafe.tc.TypeSig)sig, expressions);
	instantiations.addElement(new Instantiation(sig, expressions, newSig));

	typeParametersDecoration.set(newSig, null);
	return newSig;
	
    }
    
    
    
    
    protected EnvForTypeSig getEnvForCurrentSig(javafe.tc.TypeSig sig, boolean isStatic) {
	Env env;

	if (sig.state >= TypeSig.PREPPED) {
	     return sig.getEnv(isStatic);
	}
	env = sig.getEnv(isStatic);
	EnvForInstantiation envForCheck =
	    new EnvForInstantiation(env,
				    sig,
				    getFieldsFromStack(),
				    getMethodsFromStack(),
				    isStatic);
	//	envForCheck.display();
	return envForCheck;
    }


    FieldDeclVec getFieldsFromStack() {
	int sz = fieldSeq.size();
	FieldDecl v[] = new FieldDecl[sz];
	fieldSeq.copyInto(v);
	return FieldDeclVec.make(v);
    }

    
    MethodDeclVec getMethodsFromStack() {
	int sz = methodSeq.size();
	MethodDecl v[] = new MethodDecl[sz];
	methodSeq.copyInto(v);
	return MethodDeclVec.make(v);
    }
    
}
