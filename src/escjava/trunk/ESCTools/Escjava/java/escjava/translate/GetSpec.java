/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.translate;

import escjava.Main;
import escjava.ast.*;
import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.backpred.FindContributors;
import escjava.tc.TypeCheck;
import escjava.tc.Types;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import javafe.ast.*;
import javafe.tc.TypeSig;

import javafe.util.*;

/**
 * Responsible for getting Spec for calls.  Includes ... from ESCJ16c.
 */

public final class GetSpec
{
    public static Spec getSpecForCall(/*@ non_null */ RoutineDecl rd,
                                      /*@ non_null */ FindContributors scope,
                                      Set predictedSynTargs) {
        Spec spec = getCommonSpec( rd, scope, null );
        return extendSpecForCall( spec, scope, predictedSynTargs);
    }


    /* used for calls that are inlined */
    public static Spec getSpecForInline(/*@ non_null */ RoutineDecl rd,
                                        /*@ non_null */ FindContributors scope) {
        return getCommonSpec( rd, scope, null );
        // TBW:  Should also add NonNullInit checks somewhere!
    }


    public static Spec getSpecForBody(/*@ non_null */ RoutineDecl rd,
                                      /*@ non_null */ FindContributors scope,
                                      /*@ non_null */ Set synTargs,
                                      Hashtable premap) {
        Spec spec = getCommonSpec( rd, scope, premap );
        return extendSpecForBody( spec, scope, synTargs );
    }

    private static /*@ non_null @*/ Spec getCommonSpec(/*@ non_null */ RoutineDecl rd,
                                                       /*@ non_null */ FindContributors scope,
                                                       Hashtable premap)
    {
	/* Need to typecheck TypeDecl containing callee so that
         requires/ensures/modifies clauses etc are resolved. */

	TypeSig T = TypeSig.getSig( rd.parent );
	T.typecheck();
	
	DerivedMethodDecl combined = getCombinedMethodDecl(rd);
	DerivedMethodDecl filtered = filterMethodDecl(combined, scope);

	/*
	 * If we are translating the spec for an inner-class
	 * constructor, then we need to substitute this$0arg for
	 * this.this$0 everywhere:
	 */
	Spec spec = null;
	try {
	    if (filtered.isConstructor() && !T.isTopLevelType()) {
		Inner.firstThis0 = Inner.getEnclosingInstanceArg(
					 (ConstructorDecl)filtered.original);
	    }

	    spec = trMethodDecl(filtered, premap);
	} finally {
	    Inner.firstThis0 = null;
	}

	return spec;
    }

    static private ASTDecoration dmdDecoration = new ASTDecoration("dmd");

    /**
     ** Implement GetCombinedMethodDecl from ESCJ 16c section 7:<p>
     **
     ** Precondition: the type declaring rd has been typechecked.<p>
     **
     ** Note: this routine may typecheck the supertypes of the type that
     ** declares rd.
     **/
    //@ ensures \result != null;
    public static DerivedMethodDecl getCombinedMethodDecl(/*@ non_null */ RoutineDecl rd) {
	DerivedMethodDecl dmd = (DerivedMethodDecl)dmdDecoration.get(rd);
	if (dmd != null) return dmd;

	dmd = new DerivedMethodDecl(rd);
	dmdDecoration.set(rd,dmd);

	dmd.throwsSet = rd.raises;
	dmd.requires  = ExprModifierPragmaVec.make();
	dmd.modifies  = ModifiesGroupPragmaVec.make();
	dmd.ensures   = ExprModifierPragmaVec.make();
	dmd.exsures   = VarExprModifierPragmaVec.make();

	if (rd instanceof ConstructorDecl) {
	    // Handle constructor case:
	    dmd.args = rd.args;
	    TypeSig thisType = TypeSig.getSig(rd.parent);
	    if (!thisType.isTopLevelType()) {
		// An Inner class; add this$0 argument:
		dmd.args = rd.args.copy();
		FormalParaDecl this0arg =
		    Inner.getEnclosingInstanceArg((ConstructorDecl)rd);
		dmd.args.insertElementAt(this0arg, 0);
	    }

	    dmd.returnType = thisType;
	    addModifiersToDMD(dmd, rd);

	} else {
            // Handle method case:
            //@ assume rd instanceof MethodDecl;

            MethodDecl md = (MethodDecl)rd;
            dmd.returnType = md.returnType;

            if (Modifiers.isStatic(rd.modifiers)) {
                // static method
                dmd.args = rd.args;
            } else {
                // instance method
                dmd.args = md.args.copy();
                dmd.args.insertElementAt((FormalParaDecl)GC.thisvar.decl, 0);
            }
    
            /*
             * Add modifiers from this method as well as all methods it
             * overrides; also handle non_null:
             */
            addModifiersToDMD(dmd, md);
            Set overrides = escjava.tc.FlowInsensitiveChecks.getAllOverrides(md);
            Enumeration enum = overrides.elements();
            while (enum.hasMoreElements()) {
                MethodDecl smd = (MethodDecl)enum.nextElement();
                TypeSig.getSig(smd.parent).typecheck();

                addModifiersToDMD(dmd, smd);
            }
	}

	dmd.computeFreshUsage();

	return dmd;
    }

    /**
     ** Add the modifiers of rd to dmd, making any necessary substitions
     ** of parameter names.  Also propagates non_null's.<p>
     **
     ** Precondition: rd has been typechecked.<p>
     **/
    private static void addModifiersToDMD(/*@ non_null */ DerivedMethodDecl dmd,
					  /*@ non_null */ RoutineDecl rd) {
	/*
	 * Compute the substitution on parameter names to change a spec
	 * for an overridden method to refer to our method's parameter
	 * names instead of its; propagate non_nulls:
	 */
	Hashtable subst = new Hashtable();
	if (rd != dmd.original) {
            for (int i=0; i<rd.args.size(); i++) {
		GenericVarDecl newDecl = dmd.original.args.elementAt(i);
		GenericVarDecl oldDecl = rd.args.elementAt(i);

		// This may no longer be necessary, but it doesn't hurt
		SimpleModifierPragma nonnull = NonNullPragma(oldDecl);
		if (nonnull != null)
		    setNonNullPragma(newDecl, nonnull);

		VariableAccess va = VariableAccess.make(newDecl.id,
							Location.NULL,
							newDecl);

		subst.put(oldDecl, va);
            }
	}

	if (rd.pmodifiers == null)
	    return;

	for (int i = 0; i < rd.pmodifiers.size(); i++) {
	  // We omit pragmas that have something notimplemented, but carry on 
	  // with the rest
	  try {
	    ModifierPragma mp = rd.pmodifiers.elementAt(i);
	    switch (mp.getTag()) {
                case TagConstants.REQUIRES:
                case TagConstants.ALSO_REQUIRES:
                case TagConstants.PRECONDITION:
                    {
                        ExprModifierPragma emp = (ExprModifierPragma)mp;
                        emp = doSubst(subst, emp);
                        dmd.requires.addElement(emp);
                        break;
                    }
	        case TagConstants.MODIFIESGROUPPRAGMA:
                    {
                        ModifiesGroupPragma em = (ModifiesGroupPragma)mp;
			for (int ii=0; ii<em.items.size(); ++ii) {
			    CondExprModifierPragma emp = em.items.elementAt(ii);
			    if (emp.expr == null) {
				em.items.removeElementAt(i);
				--ii;
				continue;
			    }
			    int t = emp.expr.getTag();
			    // FIXME - no contribution to spec for these keywords
			    if (t == TagConstants.EVERYTHINGEXPR) {
				dmd.modifiesEverything = true;
			    } else if (t == TagConstants.NOTSPECIFIEDEXPR) {
				dmd.modifiesEverything = true;
			    	emp.expr = EverythingExpr.make(emp.expr.getStartLoc());
			    } else if (t == TagConstants.NOTHINGEXPR ) {
				// no action
			    }
			    emp = doSubst(subst, emp);
			    em.items.setElementAt(emp,ii);
			}
                        dmd.modifies.addElement(em);
                        break;
                    }
/*
                case TagConstants.MODIFIES:
                case TagConstants.ALSO_MODIFIES:
                case TagConstants.MODIFIABLE:
                case TagConstants.ASSIGNABLE:
                    {
                        CondExprModifierPragma emp = (CondExprModifierPragma)mp;
			if (emp.expr == null) break; // ignore - informal
			int t = emp.expr.getTag();
			// FIXME - no contribution to spec for these keywords
			if (t == TagConstants.EVERYTHINGEXPR) {
			    dmd.modifiesEverything = true;
			} else if (t == TagConstants.NOTSPECIFIEDEXPR) {
			    dmd.modifiesEverything = true;
			    //emp = doSubst(subst, 
			//	EverythingExpr.make(emp.getStartLoc()) );
				break; // FIXME
			} else if (t == TagConstants.NOTHINGEXPR ) {
			    // no action
			} else {
			}
			emp = doSubst(subst, emp);
                        dmd.modifies.addElement(emp);
                        break;
                    }
*/
                case TagConstants.ENSURES:
                case TagConstants.ALSO_ENSURES:
                case TagConstants.POSTCONDITION:
                    {
                        ExprModifierPragma emp = (ExprModifierPragma)mp;
			int t = emp.errorTag;
                        emp = doSubst(subst, emp);
			emp.errorTag = t;
                        dmd.ensures.addElement(emp);
                        break;
                    }
                case TagConstants.NON_NULL:
/*
                    if (dmd.nonnull == null) {
                        dmd.nonnull = (SimpleModifierPragma)mp;
                    }
*/
                    break;
                case TagConstants.EXSURES:
                case TagConstants.ALSO_EXSURES:
                case TagConstants.SIGNALS:
                    {
                        VarExprModifierPragma vemp = (VarExprModifierPragma)mp;
                        vemp = doSubst(subst, vemp);
                        dmd.exsures.addElement(vemp);
                        break;
                    }
                default:
                    break;
	    }
	  } catch (NotImplementedException e) {
		// Error message already printed
	  }
	}
    }


    /** Perform a substitution on an ExprModifierPragma **/
    private static ExprModifierPragma doSubst(Hashtable subst,
					      ExprModifierPragma emp) {
	return ExprModifierPragma.make(emp.tag,
				       Substitute.doSubst(subst, emp.expr),
				       emp.loc);
    }

    /** Perform a substitution on a CondExprModifierPragma **/
    private static CondExprModifierPragma doSubst(Hashtable subst,
					      CondExprModifierPragma emp) {
	return CondExprModifierPragma.make(emp.tag,
				       Substitute.doSubst(subst, emp.expr),
				       emp.loc,
		emp.cond == null ? null : Substitute.doSubst(subst, emp.cond));
    }

    /** Perform a substitution on a VarExprModifierPragma **/
    private static VarExprModifierPragma doSubst(Hashtable subst,
					         VarExprModifierPragma vemp) {
	return VarExprModifierPragma.make(vemp.tag,
					  vemp.arg,
					  Substitute.doSubst(subst, vemp.expr),
					  vemp.loc);
    }


    //@ ensures \result != null;
    public static DerivedMethodDecl filterMethodDecl(/*@ non_null */ DerivedMethodDecl dmd,
                                                     /*@ non_null */ FindContributors scope) {
        if (!Main.options().filterMethodSpecs) {
            return dmd;
        }

        DerivedMethodDecl dmdFiltered = new DerivedMethodDecl(dmd.original);
        dmdFiltered.args = dmd.args;
        dmdFiltered.returnType = dmd.returnType;
        dmdFiltered.throwsSet = dmd.throwsSet;

        dmdFiltered.requires = dmd.requires;
        dmdFiltered.modifies = filterModifies(dmd.modifies, scope);
        dmdFiltered.ensures = filterExprModPragmas(dmd.ensures, scope);
        dmdFiltered.exsures = filterVarExprModPragmas(dmd.exsures, scope);

        dmdFiltered.computeFreshUsage();

        return dmdFiltered;
    }

    private static ExprModifierPragmaVec filterExprModPragmas(/*@ non_null */ ExprModifierPragmaVec vec,
                                                              /*@ non_null */ FindContributors scope) {
        int n = vec.size();
        ExprModifierPragmaVec vecNew = null;  // lazily allocated
        for (int i = 0; i < n; i++) {
            ExprModifierPragma emp = vec.elementAt(i);
            if (exprIsVisible(scope.originType, emp.expr)) {
                // keep this pragma
                if (vecNew != null) {
                    vecNew.addElement(emp);
                }
            } else {
                // filter out this pragma
                if (vecNew == null) {
                    vecNew = ExprModifierPragmaVec.make(n-1);
                    for (int j = 0; j < i; j++) {
                        vecNew.addElement(vec.elementAt(j));
                    }
                }
            }
        }
        if (vecNew == null) {
            return vec;
        } else {
            return vecNew;
        }
    }


    private static ModifiesGroupPragmaVec filterModifies(/*@ non_null */ ModifiesGroupPragmaVec mvec,
                                                                    /*@ non_null */ FindContributors scope) {
	ModifiesGroupPragmaVec result = ModifiesGroupPragmaVec.make();
        int mn = mvec.size();
	for (int j=0; j<mn; ++j) {
	    ModifiesGroupPragma mv = mvec.elementAt(j);
	    CondExprModifierPragmaVec vec = mv.items;
	    CondExprModifierPragmaVec vecNew = null;  // lazily allocated
	    int n = vec.size();
	    for (int i = 0; i < n; i++) {
		CondExprModifierPragma vemp = vec.elementAt(i);
		if (exprIsVisible(scope.originType, vemp.expr) &&
		    exprIsVisible(scope.originType, vemp.cond)) {
		    // keep this pragma
		    if (vecNew != null) {
			vecNew.addElement(vemp);
		    }
		} else {
		    // filter out this pragma
		    if (vecNew == null) {
			vecNew = CondExprModifierPragmaVec.make(n-1);
			for (int k = 0; k < i; k++) {
			    vecNew.addElement(vec.elementAt(k));
			}
		    }
		}
	    }
	    result.addElement( ModifiesGroupPragma.make(mv.tag,mv.clauseLoc).append(vecNew == null ? vec : vecNew));
        }
	return result;
    }

    private static VarExprModifierPragmaVec filterVarExprModPragmas(/*@ non_null */ VarExprModifierPragmaVec vec,
                                                                    /*@ non_null */ FindContributors scope) {
        int n = vec.size();
        VarExprModifierPragmaVec vecNew = null;  // lazily allocated
        for (int i = 0; i < n; i++) {
            VarExprModifierPragma vemp = vec.elementAt(i);
            if (exprIsVisible(scope.originType, vemp.expr)) {
                // keep this pragma
                if (vecNew != null) {
                    vecNew.addElement(vemp);
                }
            } else {
                // filter out this pragma
                if (vecNew == null) {
                    vecNew = VarExprModifierPragmaVec.make(n-1);
                    for (int j = 0; j < i; j++) {
                        vecNew.addElement(vec.elementAt(j));
                    }
                }
            }
        }
        if (vecNew == null) {
            return vec;
        } else {
            return vecNew;
        }
    }

    //-------------------------------------------------------------------------
    //-------------------------------------------------------------------------
    //-------------------------------------------------------------------------


    /** Translates a MethodDecl to a Spec. */

    //@ ensures \result != null;
    private static Spec trMethodDecl(/*@ non_null */ DerivedMethodDecl dmd,
                                     Hashtable premap) {
        Assert.notNull(dmd);

        /*
         * Unlike any body we may be translating, for these
         * translations this's type is that of the type that contains
         * the method or constructor dmd.original.
         */
        TypeSig T = TypeSig.getSig(dmd.getContainingClass());
        Type savedType = GC.thisvar.decl.type;
        GC.thisvar.decl.type = T;
        // (we restore GC.thisvar.decl.type just before returning)


	ExprVec preAssumptions = ExprVec.make();
        ConditionVec pre = trMethodDeclPreconditions(dmd,preAssumptions);
      
        ExprVec targets  = ExprVec.make();

        if( dmd.usesFresh )
            targets.addElement( GC.allocvar );

        // translates modifies list

	for (int k=0; k<dmd.modifies.size(); ++k) {
	    Translate.ModifiesIterator ii = new Translate.ModifiesIterator(dmd.modifies.elementAt(k).items,true);
	    while (ii.hasNext()) {
		Expr designator = (Expr)ii.next();
		if (Utils.isModel(designator)) continue;
		Expr gcDesignator = TrAnExpr.trSpecExpr(designator);
		    // Returns null for modifies \nothing, \everything  FIXME?
		    // array-range, wild-ref expressions  FIXME!!
		if (gcDesignator != null) targets.addElement(gcDesignator);
	    }
	}

        // handle targets stuff, and create preVarMap

        Set roots = new Set(); // set of GenericVarDecls
      
        for(int i=0; i<targets.size(); i++)
	{
            Expr gcDesignator = targets.elementAt(i);
            VariableAccess shaved = shave( gcDesignator );
            roots.add( shaved.decl );
	}

        Hashtable preVarMap = premap;
        if (premap == null)
            preVarMap = makeSubst( roots.elements(), "pre" );
        //else
        //    preVarMap = restrict( premap, roots.elements() );

/* Re the change above: premap is a map from variables with a @pre suffix to their 
declarations; preVarMap is the relevant piece of this for the currnet method.  However,
that was determined by the set of locations specified in modifies clauses.  That leads to
erroneous behavior if the modifies clause is incorrect.  

The change is to use the premap without restriction.  That allows the verification of a body
of a method to proceed without dependence on the accuracy of the modifies clause.  However
it also adds a lot of conjuncts into the verification condition - and the premap is 
accumulated from the entire class declaration.  An improvement would be to simply use the
premap generated from the uses of \old in the body of the method + the spec of the method
+ the spec of the class.
*/
        // Now create the postconditions

	ExprVec postAssumptions = ExprVec.make();
        ConditionVec post = trMethodDeclPostcondition(dmd, preVarMap, postAssumptions);

	java.util.Set postlocs = new java.util.HashSet();
	int size = post.size();
	for (int ic = 0; ic < size; ++ic) {
		collectFields(post.elementAt(ic).pred, postlocs);
	}

        Spec spec = Spec.make(dmd, targets, preVarMap, 
				preAssumptions, pre, postAssumptions, post,
				false && dmd.modifiesEverything, postlocs); // FIXME - turning off modifies everything for now

        GC.thisvar.decl.type = savedType;
        return spec;
    }

    /** Computes the preconditions, according to section 7.2.0 of ESCJ 16. */
  
    private static ConditionVec trMethodDeclPreconditions(/*@ non_null */ DerivedMethodDecl dmd, ExprVec preAssumptions) {
        ConditionVec pre = ConditionVec.make();
      
        // Account for properties about parameters
        for (int i = 0; i < dmd.args.size(); i++) {
            FormalParaDecl arg = dmd.args.elementAt(i);
      
            if (i == 0 && arg == GC.thisvar.decl) {
                // the special parameter "this"
                addFreeTypeCorrectAs(arg, TypeSig.getSig(dmd.getContainingClass()),
                                     pre);
                VariableAccess argAccess = TrAnExpr.makeVarAccess(arg, Location.NULL);
                Expr nonnull = GC.nary(TagConstants.REFNE, argAccess, GC.nulllit);
                Condition cond = GC.freeCondition(nonnull, Location.NULL);
                pre.addElement(cond);
	
            } else {
                // regular parameters
                addFreeTypeCorrectAs(arg, arg.type, pre);
/* non_null is handled in the desugaring
                SimpleModifierPragma nonNullPragma = NonNullPragma(arg);
                if (nonNullPragma != null) {
                    VariableAccess argAccess = TrAnExpr.makeVarAccess(arg,
                                                                      Location.NULL);
                    Expr nonnull = GC.nary(TagConstants.REFNE, argAccess, GC.nulllit);
                    Condition cond = GC.freeCondition(nonnull,
                                                      nonNullPragma.getStartLoc());
                    pre.addElement(cond);
                }
*/
            }
        }

        // Add the declared preconditions

	// Make the disjunction of all of the preconditions

	java.util.Set axsToAdd = new java.util.HashSet();
	if (dmd.requires.size() != 0) {
	    Expr expr = dmd.requires.elementAt(0).expr;
	    int loc = dmd.requires.elementAt(0).getStartLoc();
	    for (int i = 1; i < dmd.requires.size(); ++i) {
		ExprModifierPragma e = dmd.requires.elementAt(i);
		if (loc == Location.NULL) loc = e.getStartLoc();
		expr = BinaryExpr.make(TagConstants.OR,expr,
			e.expr, loc);
		javafe.tc.FlowInsensitiveChecks.setType(expr,Types.booleanType);
	    }
	    TrAnExpr.initForClause();
	    Expr pred = TrAnExpr.trSpecExpr(expr);
	    if (TrAnExpr.extraSpecs) {
		preAssumptions.append(TrAnExpr.trSpecExprAuxAssumptions);
		preAssumptions.append(TrAnExpr.trSpecExprAuxConditions);
		axsToAdd.addAll(TrAnExpr.trSpecAuxAxiomsNeeded);
		TrAnExpr.closeForClause();
	    }
	    Condition cond = GC.condition(TagConstants.CHKPRECONDITION, pred,
                                          loc);

            pre.addElement(cond);
	}

	addAxioms(axsToAdd,preAssumptions);
	    
        return pre;
    }

    /** Computes the postconditions, according to section 7.2.2 of ESCJ 16. */
  
    private static ConditionVec trMethodDeclPostcondition(
			/*@ non_null */ DerivedMethodDecl dmd,
                        /*@ non_null */ Hashtable wt,
                        /*@ non_null */ ExprVec postAssumptions) {
        ConditionVec post = ConditionVec.make();

        // type correctness of targets (including "alloc", if "alloc" is a target)
        Enumeration wtEnum = wt.keys();
        while (wtEnum.hasMoreElements()) {
            GenericVarDecl vd = (GenericVarDecl)wtEnum.nextElement();
            Expr e = TrAnExpr.targetTypeCorrect(vd, wt);
            Condition cond = GC.freeCondition(e, Location.NULL);
            post.addElement(cond);
        }

        if (dmd.isConstructor()) {
            // Free:  RES != null && !isAllocated(RES, wt[[alloc]])
            Expr nonnull = GC.nary(TagConstants.REFNE, GC.resultvar, GC.nulllit);
            Expr allocated = GC.nary(TagConstants.ISALLOCATED,
                                     GC.resultvar,
                                     (VariableAccess)wt.get(GC.allocvar.decl));
            Expr notAllocated = GC.not(allocated);
            Condition cond = GC.freeCondition(GC.and(nonnull, notAllocated),
                                              Location.NULL);
            post.addElement(cond);
        }

        if (!Types.isVoidType(dmd.returnType)) {
            // Free:  TypeCorrectAs[[ RES, T ]]
            addFreeTypeCorrectAs(GC.resultvar.decl, dmd.returnType, post);
        }

        TypeSig T = TypeSig.getSig(dmd.getContainingClass());
        if (dmd.isConstructor() && !T.isTopLevelType()) {
            // Free: RES.this$0 == this$0arg
            Expr this0 = TrAnExpr.makeVarAccess(Inner.getEnclosingInstanceField(T),
                                                Location.NULL);
            FormalParaDecl this0arg =
                Inner.getEnclosingInstanceArg((ConstructorDecl)dmd.original);
            Expr thisSet = GC.nary(TagConstants.REFEQ,
                                   GC.select(this0, GC.resultvar),
                                   TrAnExpr.makeVarAccess(this0arg,Location.NULL));
            Condition cond = GC.freeCondition(thisSet, Location.NULL);
            post.addElement(cond);
        }


        if (dmd.throwsSet.size() == 0) {
            // UnexpectedException:  EC == ecReturn
            Expr pred = GC.nary(TagConstants.ANYEQ, GC.ecvar, GC.ec_return);
            Condition cond = GC.condition(TagConstants.CHKUNEXPECTEDEXCEPTION, pred,
                                          Location.NULL);
            post.addElement(cond);
        } else {
            // Free:  EC == ecThrow ==>
            //          XRES != null && typeof(XRES) <: Throwable &&
            //          isAllocated(XRES, alloc)
            Expr antecedent = GC.nary(TagConstants.ANYEQ, GC.ecvar, GC.ec_throw);
            ExprVec ev = ExprVec.make();
            // XRES != null
            Expr p = GC.nary(TagConstants.REFNE, GC.xresultvar, GC.nulllit);
            ev.addElement(p);
            // typeof(XRES) <: Throwable
            p = GC.nary(TagConstants.TYPELE,
                        GC.nary(TagConstants.TYPEOF, GC.xresultvar),
                        GC.typeExpr(Types.javaLangThrowable()));
            ev.addElement(p);
            // isAllocated(XRES, alloc)
            p = GC.nary(TagConstants.ISALLOCATED,
                        GC.xresultvar,
                        GC.allocvar);
            ev.addElement(p);
            // conjoin and add free postcondition
            Expr consequence = GC.and(ev);
            Condition cond = GC.freeCondition(GC.implies(antecedent, consequence),
                                              Location.NULL);
            post.addElement(cond);

            // UnexpectedException:
            //   EC == ecReturn ||
            //   (EC == ecThrow &&
            //     (typeof(XRES) <: X1 && ... &&& typeof(XRES) <: Xx))
            Expr normal = GC.nary(TagConstants.ANYEQ, GC.ecvar, GC.ec_return);
            Expr except = GC.nary(TagConstants.ANYEQ, GC.ecvar, GC.ec_throw);
            Expr typeofXRES = GC.nary(TagConstants.TYPEOF, GC.xresultvar);
            ev.removeAllElements();
            for (int i = 0; i < dmd.throwsSet.size(); i++) {
                TypeName x = dmd.throwsSet.elementAt(i);
                p = GC.nary(TagConstants.TYPELE, typeofXRES, GC.typeExpr(x));
                ev.addElement(p);
            }
            Expr eOutcomes;
            eOutcomes = GC.or(ev);

            p = GC.or(normal, GC.and(except, eOutcomes));

            Assert.notFalse(dmd.original.locThrowsKeyword != Location.NULL);
            cond = GC.condition(TagConstants.CHKUNEXPECTEDEXCEPTION, p,
                                Location.NULL);
            post.addElement(cond);
        }

        // constructors ensure that the new object's owner field is null
        if (dmd.isConstructor()) {
            // get java.lang.Object
            TypeSig obj = Types.javaLangObject();
	
            FieldDecl owner = null; // make the compiler happy
            boolean found = true;
	    boolean save = escjava.tc.FlowInsensitiveChecks.inAnnotation;
            try {
		escjava.tc.FlowInsensitiveChecks.inAnnotation = true;
                owner = Types.lookupField(obj, Identifier.intern("owner"),
                                          obj);
            }
            catch (javafe.tc.LookupException e) {
                found = false;
            } finally {
		escjava.tc.FlowInsensitiveChecks.inAnnotation = save;
	    }
            // if we couldn't find the owner ghost field, there's nothing to do
            if (found) {
                VariableAccess ownerVA = 
                    TrAnExpr.makeVarAccess(owner, Location.NULL);
                Expr everything;
                Expr ownerNull =  GC.nary(TagConstants.REFEQ, 
                                          GC.select(ownerVA, GC.resultvar), 
                                          GC.nulllit);
                // if there are no exceptions thrown, it is sufficient to do
                // RES.owner == null
                if (dmd.throwsSet.size() == 0)
                    everything = ownerNull;
                // else we need to do (EC == ECReturn) ==> (RES.owner == null)
                else {	    
                    Expr ret = GC.nary(TagConstants.ANYEQ, GC.ecvar, 
                                       GC.ec_return);
                    everything = GC.implies(ret, ownerNull);
                }
                Condition cond = GC.condition(TagConstants.CHKOWNERNULL,
                                              everything,
                                              Location.NULL);
                post.addElement(cond);
            }
        }
	    
        // Finally, add declared postconditions
        // First normal postconditions
        try {
            // EC == ecReturn
            Expr ante = GC.nary(TagConstants.ANYEQ, GC.ecvar, GC.ec_return);

            Hashtable map;
            if (dmd.isConstructor()) {
                map = new Hashtable();
                map.put(GC.thisvar.decl, GC.resultvar);
            } else {
                map = null;
            }
	    java.util.Set axsToAdd = new java.util.HashSet();
	    ArrayList conds = new ArrayList();
            for (int i = 0; i < dmd.ensures.size(); i++) {
	      try {
                ExprModifierPragma prag = dmd.ensures.elementAt(i);
		TrAnExpr.initForClause();
                Expr pred = TrAnExpr.trSpecExpr(prag.expr, map, wt);
		if (TrAnExpr.extraSpecs) {
		    postAssumptions.append(TrAnExpr.trSpecExprAuxAssumptions);
		    postAssumptions.append(TrAnExpr.trSpecExprAuxConditions);
		    axsToAdd.addAll(TrAnExpr.trSpecAuxAxiomsNeeded);
		    TrAnExpr.closeForClause();
		}
                pred = GC.implies(ante, pred);
		int tag = prag.errorTag == 0 ? TagConstants.CHKPOSTCONDITION : prag.errorTag;
                Condition cond = GC.condition(tag, pred, prag.getStartLoc());
		conds.add(cond);
	      } catch (NotImplementedException e) {
		    TrAnExpr.closeForClause();
			// If something not implemented occurs, a message has already
			// been issued (unless turned off by an option).  We catch it
			// at this point and go on to the next ensures clause, only
			// skipping the clause containing the construct that is not
			// implemented.
	      }
            }
	    addAxioms(axsToAdd,postAssumptions);
	    Iterator jj = conds.iterator();
	    while (jj.hasNext()) {
		post.addElement( (Condition)jj.next() );
	    }
        } finally {
	    TrAnExpr.closeForClause();
	}
/*
System.out.println("WT");
Enumeration ee = wt.keys();
while (ee.hasMoreElements()) {
	Object o = ee.nextElement();
	System.out.println("MAP: " + o + " -->> " + wt.get(o));
}
*/
        // Then exceptional postconditions
        {
            // EC == ecThrow
            Expr ante0 = GC.nary(TagConstants.ANYEQ, GC.ecvar, GC.ec_throw);
            // typeof(XRES)
            Expr typeofXRES = GC.nary(TagConstants.TYPEOF, GC.xresultvar);

	    java.util.Set axsToAdd = new java.util.HashSet();
	    ArrayList conds = new ArrayList();
            for (int i = 0; i < dmd.exsures.size(); i++) {
	      try {
                // Pragma has the form:  exsures (T v) E
                VarExprModifierPragma prag = dmd.exsures.elementAt(i);
		TrAnExpr.initForClause();
                // TrSpecExpr[[ E, {v-->XRES}, wt ]]
                Hashtable map = new Hashtable();
		Expr pred;
                if (prag.arg != null) {
		    map.put(prag.arg, GC.xresultvar);
		    pred = TrAnExpr.trSpecExpr(prag.expr, map, wt);
		    // typeof(XRES) <: T
		    Expr ante1 = GC.nary(TagConstants.TYPELE,
                                     typeofXRES, GC.typeExpr(prag.arg.type));
		    //     EC == ecThrow && typeof(XRES) <: T
		    // ==> TrSpecExpr[[ E, {v-->XRES}, wt ]]
		    pred = GC.implies(GC.and(ante0, ante1), pred);
		} else {
		    pred = TrAnExpr.trSpecExpr(prag.expr, map, wt);
		    pred = GC.implies(ante0, pred);
		}
		if (TrAnExpr.extraSpecs) {
		    postAssumptions.append(TrAnExpr.trSpecExprAuxAssumptions);
		    postAssumptions.append(TrAnExpr.trSpecExprAuxConditions);
		    axsToAdd.addAll(TrAnExpr.trSpecAuxAxiomsNeeded);
		    TrAnExpr.closeForClause();
		}
		//int tag = prag.errorTag == 0 ? TagConstants.CHKPOSTCONDITION : prag.errorTag;
		int tag = TagConstants.CHKPOSTCONDITION;
                Condition cond = GC.condition(tag, pred, prag.getStartLoc());
		conds.add(cond);
	      } catch (NotImplementedException e) {
		    TrAnExpr.closeForClause();
	      }
            }
	    addAxioms(axsToAdd,postAssumptions);
	    Iterator jj = conds.iterator();
	    while (jj.hasNext()) {
		post.addElement( (Condition)jj.next() );
	    }
        }

	// Then any initially clauses (for constructors, if not a helper)

	boolean isHelper = 
		Utils.findModifierPragma(dmd.original.pmodifiers,TagConstants.HELPER) != null; 

	if (dmd.isConstructor() && !isHelper) {
	    Hashtable map = new Hashtable();
	    map.put(GC.thisvar.decl, GC.resultvar);
	    TypeDeclElemVec pmods = dmd.getContainingClass().elems;
	    java.util.Set axsToAdd = new java.util.HashSet();
	    for (int i=0; i<pmods.size(); ++i) {
		TypeDeclElem p = pmods.elementAt(i);
		if (!(p instanceof TypeDeclElemPragma)) continue;
		if (((TypeDeclElemPragma)p).getTag() != TagConstants.INITIALLY) continue;
		ExprDeclPragma prag = (ExprDeclPragma)p;
		try {
		    TrAnExpr.initForClause();
		    Expr pred = TrAnExpr.trSpecExpr(prag.expr, map, wt);
		    if (TrAnExpr.extraSpecs) {
			postAssumptions.append(TrAnExpr.trSpecExprAuxAssumptions);
			postAssumptions.append(TrAnExpr.trSpecExprAuxConditions);
			axsToAdd.addAll(TrAnExpr.trSpecAuxAxiomsNeeded);
			TrAnExpr.closeForClause();
		    }
		    int tag = TagConstants.CHKINITIALLY;
		    Condition cond = GC.condition(tag, pred, prag.getStartLoc());
		    post.addElement(cond);
		} catch (NotImplementedException e) {
			TrAnExpr.closeForClause();
	        }
	    }
	    addAxioms(axsToAdd,postAssumptions);
        }

	if (dmd.isConstructor() || isHelper) return post;
	// Then any constraint clauses (for methods)

	TypeDecl tdecl = dmd.getContainingClass();
	Set s = new javafe.util.Set();
	if (tdecl instanceof InterfaceDecl) s.add(tdecl);
	else {
	    ClassDecl cdecl = (ClassDecl)tdecl;
	    while (true) {
		post = addConstraintClauses(post,cdecl,wt,postAssumptions);
		addSuperInterfaces(cdecl,s);
		if (cdecl.superClass == null) break;
		cdecl = (ClassDecl)TypeSig.getSig(cdecl.superClass).getTypeDecl();
	    }
	}
	Enumeration en = s.elements();
	while (en.hasMoreElements()) {
	    InterfaceDecl ifd = (InterfaceDecl)en.nextElement();
	    post = addConstraintClauses(post,ifd,wt,postAssumptions);
	}
	return post;
    }


    static public void addAxioms(java.util.Set axsToAdd, ExprVec assumptions) {
	    java.util.Set axsDone = new java.util.HashSet();
	    while (! axsToAdd.isEmpty()) {
		ASTNode o = (ASTNode)axsToAdd.iterator().next();
		axsToAdd.remove(o);
		if (!axsDone.add(o)) continue;
		Expr e = TrAnExpr.getEquivalentAxioms(o,null);
		assumptions.addElement(e);
		axsToAdd.addAll( TrAnExpr.getAxiomSet(o));
	    }
    }

// FIXME - need to include inherited constraint clauses
    static public ConditionVec addConstraintClauses(ConditionVec post, TypeDecl decl,
		Hashtable wt, ExprVec postAssumptions) {
	TypeDeclElemVec pmods = decl.elems;
	java.util.Set axsToAdd = new java.util.HashSet();
	for (int i=0; i<pmods.size(); ++i) {
	    TypeDeclElem p = pmods.elementAt(i);
	    if (!(p instanceof TypeDeclElemPragma)) continue;
	    if (((TypeDeclElemPragma)p).getTag() != TagConstants.CONSTRAINT) continue;
	    ExprDeclPragma prag = (ExprDeclPragma)p;
	    try {
		TrAnExpr.initForClause();
		Expr pred = TrAnExpr.trSpecExpr(prag.expr, null, wt);
		if (TrAnExpr.extraSpecs) {
		    postAssumptions.append(TrAnExpr.trSpecExprAuxAssumptions);
		    postAssumptions.append(TrAnExpr.trSpecExprAuxConditions);
		    axsToAdd.addAll(TrAnExpr.trSpecAuxAxiomsNeeded);
		    TrAnExpr.closeForClause();
		}
		int tag = TagConstants.CHKCONSTRAINT;
		Condition cond = GC.condition(tag, pred, prag.getStartLoc());
		post.addElement(cond);
	    } catch (NotImplementedException e) {
		    TrAnExpr.closeForClause();
	    }
	}

	addAxioms(axsToAdd,postAssumptions);
        return post;
    }

    //-------------------------------------------------------------------------
    //-------------------------------------------------------------------------
    //-------------------------------------------------------------------------

    /** Implements ExtendSpecForCall, section 7.3 of ESCJ 16. */
  
    private static Spec extendSpecForCall(/*@ non_null */ Spec spec,
                                          /*@ non_null */ FindContributors scope,
                                          Set predictedSynTargs) {
// FIXME - I'm not sure that \old variables not in the modifies list get translated here
// I think those translations are in scope but not in spec.  
// spec.preVarMap contains the modified variables for the current routine
// but it is the preVarMap in the initialState generated from scope that has the
// relevant mappings of variables mentioned in \old expressions

        // The set of variables modified by *this* GC call:
        Set modifiedVars = new Set( spec.preVarMap.keys() );
    
        ParamAndGlobalVarInfo vars = null;

	boolean isConstructor = spec.dmd.isConstructor();
        for (InvariantInfo ii = mergeInvariants(collectInvariants(scope, spec.preVarMap));
             ii != null; ii = ii.next) {

	    int tag = ii.prag.getTag();
	    boolean includeInPre = true;
	    boolean includeInPost = tag != TagConstants.AXIOM;

            /*
             * Does ii mention a variable that this GC call will modify?
             */
            Set invFV = Substitute.freeVars( ii.J );
            boolean mentionsModifiedVars = Main.options().useAllInvPostCall ||
                invFV.containsAny(modifiedVars) || spec.modifiesEverything;

            /*
             * Does ii mention a variable that the body that is making the
             * GC call ever modifies?
             */
            boolean falsifiable = true;
            if (predictedSynTargs != null || spec.modifiesEverything) {
                Assert.notFalse(!Main.options().useAllInvPreBody);
                falsifiable = invFV.containsAny(predictedSynTargs);
            }

            if (ii.isStatic) {
                // static invariant

                // PRECONDITION for static invariant
                Condition cond = GC.condition(TagConstants.CHKOBJECTINVARIANT, ii.J,
                                              ii.prag.getStartLoc());
                if (falsifiable && includeInPre)
                    spec.pre.addElement(cond);

                // POSTCONDITION for static invariant

                if( mentionsModifiedVars ) {
                    // The free variables of "J" overlap with "synTargs", so add "J"
                    cond = GC.freeCondition(ii.J, ii.prag.getStartLoc());
                    if (includeInPost) spec.post.addElement(cond);
                }
      
            } else {
                // instance invariant
                Assert.notNull(ii.sdecl);
                Assert.notNull(ii.s);

                if (falsifiable) {
                    // PRECONDITION for instance invariant
	
                    // Gather parameters and static fields, unless already cached
                    if (vars == null) {
                        vars = collectParamsAndGlobals(spec, scope);
                    }

                    /* 
                     * Without any optimizations, we would generate one precondition here,
                     *
                     *   p == null || !is(p, trType[[ U ]])
                     *             || TrSpecExpr[[ J, {this-->p}, {} ]]
                     *
                     * for each parameter or static field "p", where U is the
                     * type of this in invariant J.
                     *
                     *
                     * Optimizations:
                     *
                     *   - First, generate no preconditions for any p such that we
                     *     can prove statically that p cannot have type U at
                     *     runtime.
                     *
                     *   - Second, combine all the remaining preconditions into 1
                     *     universally quantified precondition:
                     *
                     *         (FORALL s :: (s == p0 || s == p1 || ...)
                     *              ==> s == null || !is(s, trType[[ U ]]
                     *                            || TrSpecExpr[[ J, {this-->p}, {} ]] )
                     *
                     *     where "p0", "p1", ... are the parameters and static
                     *     fields.  If the list "p0", "p1", ... is empty, don't generate
                     *     a precondition.
                     *
                     *   - Third, if all of the p_i's are "non_null", drop the disjunct
                     *     "s == null".
                     *
                     *   - Fourth, if all of the p_i's can be proved to be statically of
                     *     type U, drop the disjunct "!is(s, trType[[ U ]]".
                     */

                    // Build equalities & collect info on which disjuncts to include:
                    boolean allAreNonnull = true;
                    boolean allAreOfTypeU = true;
                    ExprVec alternatives = ExprVec.make();

                    for (ParamAndGlobalVarInfo info = vars;
                         info != null; info = info.next) {
                        if (!Types.isSubclassOf(info.U, ii.U)) {
                            // p may not always/never hold an object of type U (ii.U)
                            if (!Types.isSubclassOf(ii.U, info.U))
                                // p can never hold an object of type U (ii.U)
                                continue;
                            allAreOfTypeU = false;
                        }

                        Expr eq = GC.nary(TagConstants.REFEQ,
                                          ii.s, TrAnExpr.makeVarAccess(info.vdecl,
                                                                       Location.NULL));
                        alternatives.addElement(eq);
                        //if (! info.isNonnull) // FIXME
                            allAreNonnull = false;
                    }


                    /*
                     * -noOutCalls changes this to check *in addition* all
                     * non-null allocated objects of dynamic type U *except*
                     * objectToBeConstructed:
                     */
                    if (Main.options().noOutCalls) {
                        // isAllocated(ii.s, alloc [in pre-state])
                        Expr isAllocated = GC.nary(TagConstants.ISALLOCATED,
                                                   ii.s,
                                                   GC.allocvar);
                        Expr notEq = GC.nary(TagConstants.REFNE, ii.s,
                                             GC.objectTBCvar);

                        alternatives.addElement(GC.and(isAllocated, notEq));
                        allAreNonnull = false;
                        allAreOfTypeU = false;
                    }


                    // build precondition if any alternatives:
                    if (alternatives.size() != 0) {
                        Expr ante = GC.or(alternatives);
                        Expr cons = ii.J;

                        ExprVec disjuncts = ExprVec.make();
                        if (!allAreNonnull)
                            disjuncts.addElement(GC.nary(TagConstants.REFEQ, ii.s,
                                                         GC.nulllit));
                        if (!allAreOfTypeU)
                            disjuncts.addElement(GC.not(GC.nary(TagConstants.IS, ii.s,
                                                                TrAnExpr.trType(ii.U))));
                        if (disjuncts.size()!=0) {
                            disjuncts.addElement(cons);
                            cons = GC.or(disjuncts);
                        }

                        Expr quant = GC.forall(ii.sdecl, GC.implies(ante, cons));
                        Condition cond = GC.condition(TagConstants.CHKOBJECTINVARIANT,
                                                      quant, ii.prag.getStartLoc());
                        if (includeInPre) spec.pre.addElement(cond);
                    }
                }

                // POSTCONDITION for instance invariant
	
                if (mentionsModifiedVars && includeInPost) {
                    // TypeCorrectNoallocAs[[ s, U ]] && s != null
                    ExprVec ev = TrAnExpr.typeAndNonNullAllocCorrectAs(ii.sdecl, ii.U,
                                                                       null, true,
                                                                       null, false);
                    ExprVec nopats = ev.copy();

                    Expr p  = TrAnExpr.trSpecExpr(ii.prag.expr,
                                                 TrAnExpr.union(spec.preVarMap, ii.map),
                                                 null);
		    if (spec.modifiesEverything) collectFields(p, spec.postconditionLocations);
                    if (includeInPre) ev.addElement(p);

                    Expr ante = GC.and(ev);
                    Expr impl = GC.implies(ante, ii.J);

                    spec.post.addElement(GC.freeCondition(GC.forall(ii.sdecl, impl,
                                                                    nopats),
                                                          ii.prag.getStartLoc()));
                }
            }
        }
    
        return spec;
    }

    /** Implements ExtendSpecForBody, section 7.4 of ESCJ 16. */
  
    private static Spec extendSpecForBody(/*@ non_null */ Spec spec,
                                          /*@ non_null */ FindContributors scope,
                                          /*@ non_null */ Set synTargs) {
    
	TypeDecl td = spec.dmd.getContainingClass();
	boolean isConstructor = spec.dmd.isConstructor();

        // Add NonNullInit checks
        if (isConstructor &&
            !spec.dmd.isConstructorThatCallsSibling()) {
            // first check fields in first-inherited interfaces
	    ClassDecl cd = (ClassDecl)td;
            Enumeration enum = getFirstInheritedInterfaces(cd);
            while (enum.hasMoreElements()) {
                TypeDecl tdSuperInterface = (TypeDecl)enum.nextElement();
                nonNullInitChecks(tdSuperInterface, spec.post);
            }
            // then check fields in the current class
            nonNullInitChecks(td, spec.post);
        }

        for (InvariantInfo ii = mergeInvariants(collectInvariants(scope,spec.preVarMap));
             ii != null; ii = ii.next) {
	    int tag = ii.prag.getTag();
            addInvariantBody(ii, spec, synTargs);
        }

        ExprVec axioms = collectAxioms(scope);
    
        for(int i=0; i<axioms.size(); i++) {
            spec.pre.addElement( GC.freeCondition( axioms.elementAt(i),
                                                   Location.NULL ) );
        }

        return spec;
    }

    /** Add to <code>post</code> all NonNullInit checks for non_null
     * instance fields and instance ghost fields declared in <code>td</code>.
     **/
    private static void nonNullInitChecks(/*@ non_null */ TypeDecl td,
                                          /*@ non_null */ ConditionVec post) {
        TypeDeclElemVec tdes = td.elems;

        // check that non_null instance fields have been initialized
        for (int i = 0; i < tdes.size(); i++) {
            TypeDeclElem tde = tdes.elementAt(i);
            FieldDecl fd;
            if (tde.getTag() == TagConstants.FIELDDECL) {
                fd = (FieldDecl)tde;
            } else if (tde.getTag() == TagConstants.GHOSTDECLPRAGMA) {
                fd = ((GhostDeclPragma)tde).decl;
            } else {
                continue;
            }

            if (!Modifiers.isStatic(fd.modifiers)) {
                SimpleModifierPragma smp = NonNullPragma(fd);
                if (smp != null) {
                    // NonNullInit: EC==ecReturn ==> f[RES] != null

                    Expr left = GC.nary(TagConstants.ANYEQ,GC.ecvar, GC.ec_return);
		
                    VariableAccess f = TrAnExpr.makeVarAccess(fd, Location.NULL);
                    Expr right = GC.nary(TagConstants.REFNE,
                                         GC.select(f, GC.resultvar),
                                         GC.nulllit);
                    Expr pred = GC.implies(left, right);
                    Condition cond = GC.condition(TagConstants.CHKNONNULLINIT,
                                                  pred, smp.getStartLoc());
                    post.addElement(cond);
                }
            }
        }
    }
  
    //@ ensures \result != null && \result.elementType == \type(InterfaceDecl);
    static public Enumeration getFirstInheritedInterfaces(
                                                          /*@non_null*/ ClassDecl cd) {
        Set interfaces = new Set();
        addSuperInterfaces(cd, interfaces);
        if (interfaces.size() != 0 && cd.superClass != null) {
            TypeDecl tdSuper = TypeSig.getSig(cd.superClass).getTypeDecl();
            Set superClassInterfaces = new Set();
            addSuperInterfaces(tdSuper, superClassInterfaces);
            Enumeration enum = superClassInterfaces.elements();
            while (enum.hasMoreElements()) {
                interfaces.remove(enum.nextElement());
            }
        }
        return interfaces.elements();
    }

    //@ requires set.elementType == \type(InterfaceDecl);
    private static void addSuperInterfaces(/*@ non_null */ TypeDecl td,
                                           /*@ non_null */ Set set) {
        if (td instanceof InterfaceDecl) {
            set.add(td);
        }
        // add superinterfaces of "td"
        TypeNameVec si = td.superInterfaces;
        for (int i = 0; i < si.size(); i++) {
            TypeName superName = si.elementAt(i);
            TypeDecl superDecl = TypeSig.getSig(superName).getTypeDecl();
            addSuperInterfaces(superDecl, set);
        }
    }


    /** Extend <code>spec</code>, in a way appropriate for checking the
     * body of a method or constructor, to account for invariant <code>ii.J</code>
     * declared in class <code>ii.U</code>.
     * The body to be checked has syntactic targets <code>synTargs</code>.
     **/

    private static void addInvariantBody(/*@ non_null */ InvariantInfo ii,
                                         /*@ non_null */ Spec spec,
                                         /*@ non_null */ Set synTargs) {


        Set invFV = Substitute.freeVars( ii.J );

        /* Include invariant in post only if intersection of vars of
         invariant and vars modified in the method body is nonempty. */
	// Also include it if we are dealing with a constructor, since then
	// the invariant might never have been established.

	boolean isConstructor = spec.dmd.isConstructor();
	boolean includeInPre = true;
	boolean includeInPostOrig = true;
        boolean includeInPost = includeInPostOrig && (Main.options().useAllInvPostBody ||
            invFV.containsAny(synTargs));

        if (ii.isStatic) {
            // static invariant

            Condition cond = GC.freeCondition(ii.J, ii.prag.getStartLoc());

            if (includeInPre) spec.pre.addElement(cond);
      
            if (includeInPost) {
                cond = GC.condition(TagConstants.CHKOBJECTINVARIANT, ii.J,
                                    ii.prag.getStartLoc());
                spec.post.addElement(cond);
            }
      
        } else {
            // instance invariant

            // Do the precondition
            {
                // Method, or constructor not declared below:
                //   (FORALL s :: TypeCorrectNoallocAs[[ s, U ]] && s != null ==> J)
                //
                // Constructor of a class T, where either
                //   *  U is a subtype of T, and
                //      either U is not T or the constructor does not call a sibling
                // or
                //   *  U is an interface, and
                //        +  m calls sibling constructor and U is not a
                //           superinterface of T
                //        or
                //        +  m does not call sibling constructor and U is not a
                //           superinterface of a proper superclass of T
                //   (FORALL s :: TypeCorrectNoallocAs[[ s, U ]] && s != null &&
                //                s != objectToBeConstructed
                //            ==> J)
                //
                // In either case, NOPATS is the same as the antecedent.
                ExprVec ante = TrAnExpr.typeAndNonNullAllocCorrectAs(ii.sdecl, ii.U,
                                                                     null, true,
                                                                     null, false);
                if (spec.dmd.isConstructor()) {
                    TypeSig tU = ii.U;
                    TypeSig tT = TypeSig.getSig(spec.dmd.getContainingClass());
                    boolean includeAntecedent = false;
                    if (Types.isSubclassOf(tU, tT)) {
                        if (!Types.isSameType(tU, tT) ||
                            !spec.dmd.isConstructorThatCallsSibling()) {
                            includeAntecedent = true;
                        }
                    } else if (ii.prag.parent instanceof InterfaceDecl) {
                        if (spec.dmd.isConstructorThatCallsSibling()) {
                            if (!Types.isSubclassOf(tT, tU)) {
                                includeAntecedent = true;
                            }
                        } else {
                            ClassDecl cd = (ClassDecl)spec.dmd.getContainingClass();
                            if (!Types.isSubclassOf(TypeSig.getSig(cd.superClass), tU)) {
                                includeAntecedent = true;
                            }
                        }
                    }
                    if (includeAntecedent) {
                        Expr p = GC.nary(TagConstants.REFNE, ii.s, GC.objectTBCvar);
                        ante.addElement(p);
                    }
                }
		Expr body = GC.implies(GC.and(ante), ii.J);
		Expr quant = GC.forall(ii.sdecl, body, ante);
		Condition cond = GC.freeCondition(quant, ii.prag.getStartLoc());
		if (includeInPre) spec.pre.addElement(cond);
            }

            // Do the postcondition
      
            // Include the invariant as a checked postcondition if its free variables
            // overlap with the syntactic targets of the body (as indicated by the
            // current value of "includeInPost"), or if the routine is a constructor
            // (that does not call a sibling) of some class "T" and the invariant is
            // declared in "T" or in one of "T"'s first-inherited interfaces.
            if (!includeInPost && spec.dmd.isConstructor() &&
                !spec.dmd.isConstructorThatCallsSibling()) {
                TypeSig tU = ii.U;
                ClassDecl cd = (ClassDecl)spec.dmd.getContainingClass();
                TypeSig tT = TypeSig.getSig(cd);
                if (Types.isSubclassOf(tT, tU) &&
                    (cd.superClass == null ||
                     !Types.isSubclassOf(TypeSig.getSig(cd.superClass), tU))) {
                    // "U" is "T" or a first-inherited interface of "T"
                    includeInPost = true;
                }
            }

            if (includeInPost && includeInPostOrig) {
                // TypeCorrectAs[[ s, U ]] && s != null
                ExprVec ante = TrAnExpr.typeAndNonNullAllocCorrectAs(
							ii.sdecl, ii.U,
							 null, true,
							 null, true);
	
                if (spec.dmd.isConstructor()) {
                    TypeSig tU = ii.U;
                    TypeSig tT = TypeSig.getSig(spec.dmd.getContainingClass());
                    if (!Types.isSubclassOf(tT, tU)) {
                        // "m" is a constructor, and "U" is not a superclass or
                        // superinterface of "T"
                        // Add to antecedent the conjunct:  s != this
                        ante.addElement(GC.nary(TagConstants.REFNE, ii.s, GC.thisvar));
                    } else if (Types.isSameType(tU, tT) &&
                               spec.dmd.throwsSet.size() != 0) {
                        // "m" is a constructor, and "U" is "T", and throws set is nonempty
                        // Add to antecedent the conjunct:  (EC == ecReturn || s != this)
                        ante.addElement(
                                        GC.or(GC.nary(TagConstants.ANYEQ, GC.ecvar, GC.ec_return),
                                              GC.nary(TagConstants.REFNE, ii.s, GC.thisvar)));
                    }
                }
		Expr body = GC.implies(GC.and(ante), ii.J);
		Expr quant = GC.forall(ii.sdecl, body);
		Condition cond = GC.condition(TagConstants.CHKOBJECTINVARIANT, quant,
					      ii.prag.getStartLoc());
		spec.post.addElement(cond);
                if (Info.on) {
                    Info.out("[addInvariantBody: Including body-post-invariant at " +
                             Location.toString(ii.prag.getStartLoc()) + "]");
                }
            } else {
                if (Info.on) {
                    Info.out("[addInvariantBody: Skipping body-post-invariant at " +
                             Location.toString(ii.prag.getStartLoc()) + "]");
                }
            }
        }
    }
  
    /** Collects the axioms in <code>scope</code>. */
  
    private static ExprVec collectAxioms(/*@ non_null */ FindContributors scope) {

        ExprVec r = ExprVec.make();

	TrAnExpr.initForClause();
        for( Enumeration enum = scope.typeSigs();
             enum.hasMoreElements(); )
        {

            TypeDecl td = ((javafe.tc.TypeSig)enum.nextElement()).getTypeDecl();

            for (int i = 0; i < td.elems.size(); i++) {
                TypeDeclElem tde = td.elems.elementAt(i);
                if (tde.getTag() == TagConstants.AXIOM) {
                    ExprDeclPragma axiom = (ExprDeclPragma)tde;
                    if (!Main.options().filterInvariants ||
                        exprIsVisible(scope.originType, axiom.expr)) {
                        r.addElement( TrAnExpr.trSpecExpr( axiom.expr, null, null ) );
                    }
                } else if (tde.getTag() == TagConstants.REPRESENTS &&
				Main.options().useFcnsForModelVars ) {
		    NamedExprDeclPragma p = (NamedExprDeclPragma)tde;
		    FieldDecl fd = ((FieldAccess)p.target).decl;
		    Expr e = TrAnExpr.getRepresentsAxiom(p,null);
		    ExprVec ev = (ExprVec)Utils.axiomDecoration.get(fd);
		    if (ev == null) ev = ExprVec.make(10);
		    ev.addElement(e);
		    Utils.axiomDecoration.set(fd,ev);
		    r.addElement( e );
		}
            }
        }

	TrAnExpr.closeForClause();
        return r;
    }

    /** Collects the invariants in <code>scope</code>. */
  
    private static InvariantInfo collectInvariants(/*@ non_null */ FindContributors scope, Hashtable premap) {
        InvariantInfo ii = null;
        InvariantInfo iiPrev = null;

        Enumeration enum = scope.invariants();
	try {
	  TrAnExpr.initForClause();
          while (enum.hasMoreElements()) {
            ExprDeclPragma ep = (ExprDeclPragma)enum.nextElement();
            Expr J = ep.expr;

            boolean Jvisible = !Main.options().filterInvariants ||
                exprIsVisible( scope.originType, J );
	  
           // System.out.print( (Jvisible?"Visible":"Invisible")+": ");
           // javafe.ast.PrettyPrint.inst.print(System.out, 0, J );
           // System.out.println();
	  
            if( Jvisible ) {
//System.out.println("COLLECTING INVARIANT " + Location.toString(ep.getStartLoc()));

                // Add a new node at the end of "ii"
                InvariantInfo invinfo = new InvariantInfo();
                invinfo.prag = ep;
                invinfo.U = TypeSig.getSig(ep.parent);
                if (iiPrev == null)
                    ii = invinfo;
                else
                    iiPrev.next = invinfo;
                iiPrev = invinfo;
	    
                // The following determines whether or not an invariant is a
                // static invariant by, in essence, checking for occurrence
                // of "this" in the guarded-command translation of "J", not
                // in "J" itself.  (These yield different results in the
                // unusual case that "J" mentioned "this" in a subexpression
                // "E.g", where "g" is a static field.)
                //  First, build the map "{this-->s}" for a new "s".

                LocalVarDecl sdecl = UniqName.newBoundThis();
                VariableAccess s = TrAnExpr.makeVarAccess(sdecl, Location.NULL);
                Hashtable map = new Hashtable();
		map.put(GC.thisvar.decl, s);

                int cReplacementsBefore = TrAnExpr.getReplacementCount();

                /*
                 * Unlike any body we may be translating, for these
                 * translations this's type is that of the type that contains
                 * the invariant J.
                 */
                Type savedType = GC.thisvar.decl.type;
                GC.thisvar.decl.type = TypeSig.getSig(ep.getParent());
		invinfo.J = TrAnExpr.trSpecExpr(J, map, null);
		if (TrAnExpr.trSpecExprAuxConditions.size() != 0) {
		    // Use andx here, because the op needs to be and in preconditions and 
		    // implies in postconditions
		    invinfo.J = GC.andx( GC.nary(TagConstants.BOOLAND, 
					 TrAnExpr.trSpecExprAuxConditions),
					 invinfo.J);
		    TrAnExpr.trSpecExprAuxConditions = ExprVec.make();
		}
                GC.thisvar.decl.type = savedType;

                if (cReplacementsBefore == TrAnExpr.getReplacementCount()) {
                    // static invariant
                    invinfo.isStatic = true;
                    invinfo.sdecl = null;
                    invinfo.s = null;
                    invinfo.map = null;
                } else {
                    invinfo.isStatic = false;
                    invinfo.sdecl = sdecl;
                    invinfo.s = s;
                    invinfo.map = map;
                }
//System.out.println("COLLECTING INVARIANT-END " + Location.toString(ep.getStartLoc()));
            }
          }
	  java.util.Set axsToAdd = new java.util.HashSet();
	  axsToAdd.addAll(TrAnExpr.trSpecAuxAxiomsNeeded);
	  java.util.Set axsDone = new java.util.HashSet();
	    while (false && ! axsToAdd.isEmpty()) {  // FIXME - keep this off ???
		ASTNode o = (ASTNode)axsToAdd.iterator().next();
		axsToAdd.remove(o);
		if (!axsDone.add(o)) continue;
		Expr e = TrAnExpr.getEquivalentAxioms(o,null);
		axsToAdd.addAll( TrAnExpr.getAxiomSet(o));
                // Add a new node at the end of "ii"
                InvariantInfo invinfo = new InvariantInfo();
		invinfo.J = e;
                invinfo.prag = ExprDeclPragma.make(TagConstants.AXIOM, e, Location.NULL);
                // FIXME invinfo.U = TypeSig.getSig(ep.parent);
                if (iiPrev == null)
                    ii = invinfo;
                else
                    iiPrev.next = invinfo;
                iiPrev = invinfo;
                if (true ) { //|| cReplacementsBefore == TrAnExpr.getReplacementCount())  // FIXME
                    // static invariant
                    invinfo.isStatic = true;
                    invinfo.sdecl = null;
                    invinfo.s = null;
                    invinfo.map = null;
                } else {
                    invinfo.isStatic = false;
                    // FIXME invinfo.sdecl = sdecl;
                    // FIXME invinfo.s = s;
                    // FIXME invinfo.map = map;
                }
	    }
	} finally {
	  TrAnExpr.closeForClause();
	}

        return ii;
    }

    /** Collects the parameters of <code>spec.args</code> and the static
     * fields in <code>scope</code>, whose types are class types.
     **/
  
    private static ParamAndGlobalVarInfo collectParamsAndGlobals(
                                                                 /*@ non_null */ Spec spec,
                                                                 /*@ non_null */ FindContributors scope) {
        ParamAndGlobalVarInfo vars = null;
        ParamAndGlobalVarInfo varPrev = null;

        // Add the parameters
        for (int i = 0; i < spec.dmd.args.size(); i++) {
            FormalParaDecl arg = spec.dmd.args.elementAt(i);
            TypeSig classSig;
            boolean isNonnull;
            if (i == 0 && arg == GC.thisvar.decl) {
                classSig = TypeSig.getSig(spec.dmd.getContainingClass());
		isNonnull = true;
            } else {
                classSig = Types.toClassTypeSig(arg.type);
                isNonnull = NonNullPragma(arg) != null; 
		isNonnull = false; // FIXME
            }
      
            if (classSig != null) {
                // The parameter is of a class type
                ParamAndGlobalVarInfo info = new ParamAndGlobalVarInfo();
                if (varPrev == null)
                    vars = info;
                else
                    varPrev.next = info;
                varPrev = info;

                info.vdecl = arg;
                info.U = classSig;
                info.isNonnull = isNonnull;
            }
        }

        // Add the static fields
        Enumeration enum = scope.fields();
        while (enum.hasMoreElements()) {
            FieldDecl fd = (FieldDecl)enum.nextElement();

            TypeSig classSig = Types.toClassTypeSig(fd.type);
	  
            if (classSig != null && Modifiers.isStatic(fd.modifiers) ) {
                // the field is a static field of a class type
                ParamAndGlobalVarInfo info = new ParamAndGlobalVarInfo();
                if (varPrev == null)
                    vars = info;
                else
                    varPrev.next = info;
                varPrev = info;

                info.vdecl = fd;
                info.U = classSig;
                info.isNonnull = NonNullPragma(fd) != null;
            }
        }

        return vars;
    }

    /** Shaves a GC designator. */
  
    private static VariableAccess shave(/*@ non_null */ Expr e)
    {
        switch( e.getTag() )
	{
            case TagConstants.VARIABLEACCESS:
                return (VariableAccess)e;

            case TagConstants.SELECT:
                return shave( ((NaryExpr)e).exprs.elementAt(0) );

            default:
                Assert.fail("Unexpected case: " + " " 
			+ TagConstants.toString(e.getTag()) + " "
			+ e + " " + Location.toString(e.getStartLoc()));
                return null;
	}
    }

    /** Creates and returns a new map that is <code>map</code> restricted
     * to the domain <code>e</code>.  Assumes that every element in
     * <code>e</code> is in the domain of <code>map</code>.
     **/

    //@ requires map.keyType == \type(GenericVarDecl);
    //@ requires map.elementType == \type(VariableAccess);
    //@ requires e.elementType == \type(GenericVarDecl);
    static Hashtable restrict(/*@ non_null */ Hashtable map,
                              /*@ non_null */ Enumeration e) {
        Hashtable r = new Hashtable();
        while (e.hasMoreElements()) {
            GenericVarDecl vd = (GenericVarDecl)e.nextElement();
            VariableAccess variant = (VariableAccess)map.get(vd);
            Assert.notNull(variant);
            r.put(vd, variant);
        }
        return r;
    }
  
    /** Converts a GenericVarDecl enumeration to a mapping from those
     variables to new Variableaccesses. */
  
    //@ requires e.elementType == \type(GenericVarDecl);
    static Hashtable makeSubst(/*@ non_null */ Enumeration e,
                               /*@ non_null */ String postfix )
    {
        Hashtable r = new Hashtable();
        while( e.hasMoreElements() )
	{
            GenericVarDecl vd = (GenericVarDecl)e.nextElement();
            VariableAccess variant = createVarVariant( vd, postfix );
            r.put( vd, variant );
	}
        return r;
    }

    static Hashtable makeSubst(/*@ non_null */ FormalParaDeclVec args,
                               /*@ non_null */ String postfix) {
        Hashtable r = new Hashtable();
        for (int i = 0; i < args.size(); i++) {
            GenericVarDecl vd = args.elementAt(i);
            VariableAccess variant = createVarVariant(vd, postfix);
            r.put(vd, variant);
        }
        return r;
    }


    /**
     ** Given a GenericVarDecl named "x@old", returns a VariableAccess to a
     ** fresh LocalVarDecl named "x@<postfix>".
     **
     ** This handles ESCJ 23b case 13.
     **/
    static VariableAccess createVarVariant(/*@ non_null */ GenericVarDecl vd,
                                           /*@ non_null */ String postfix) {
        String name = vd.id.toString();
        if (name.indexOf('@')!= -1)
            name = name.substring(0, name.indexOf('@'));

        Identifier id = Identifier.intern( name+"@"+postfix );
        LocalVarDecl ld =
            LocalVarDecl.make( vd.modifiers,
                               vd.pmodifiers,
                               id,
                               vd.type,
                               vd.locId,
                               null, Location.NULL );
        VariableAccess va = VariableAccess.make( id, vd.locId, ld );

        return va;
    }


    /** Adds to <code>cv</code> a condition stating that <code>vd</code>
     * has type <code>type</code>.
     **/
      
    private static void addFreeTypeCorrectAs(GenericVarDecl vd, Type type,
                                             ConditionVec cv) {
        Expr e = TrAnExpr.typeCorrectAs(vd, type);
        Condition cond = GC.freeCondition(e, Location.NULL);
        cv.addElement(cond);
    }

    /** Returns a command that first does an <code>assume</code> for
     * each precondition in <code>spec</code>, then does <code>body</code>,
     * then checks the postconditions of <code>spec</code>, and finally
     * checks the modifies constraints implied by <code>spec</code>.
     **/
  
    public static GuardedCmd surroundBodyBySpec(GuardedCmd body, Spec spec,
                                                FindContributors scope,
                                                Set syntargets,
                                                Hashtable premap,
                                                int locEndCurlyBrace) {
        StackVector code = new StackVector();
        code.push();

	addAssumptions(spec.preAssumptions, code);
        assumeConditions(spec.pre, code);
        code.addElement(body);
	addAssumptions(spec.postAssumptions, code);
        checkConditions(spec.post, locEndCurlyBrace, code);
        checkModifiesConstraints(spec, scope, syntargets, premap,
                                 locEndCurlyBrace, code);

        return GC.seq(GuardedCmdVec.popFromStackVector(code));
    }

    /** Appends <code>code</code> with an <code>assume C</code> command
     * for every condition <code>C</code> in <code>cv</code>.
     **/

    private static void addAssumptions(ExprVec ev, StackVector code) {
        for (int i = 0; i < ev.size(); i++) {
            Expr e = ev.elementAt(i);
            code.addElement(GC.assume(e));
        }
    }
  
    private static void assumeConditions(ConditionVec cv, StackVector code) {
        for (int i = 0; i < cv.size(); i++) {
            Condition cond = cv.elementAt(i);
            code.addElement(GC.assumeAnnotation(cond.locPragmaDecl, cond.pred));
        }
    }
  
    /** Appends <code>code</code> with an <code>check loc: C</code>
     * command for every condition <code>C</code> in <code>cv</code>.
     **/
  
    private static void checkConditions(ConditionVec cv, int loc, StackVector code) {
        for (int i = 0; i < cv.size(); i++) {
            Condition cond = cv.elementAt(i);
            Translate.setop(cond.pred);
            // if the condition is an object invariant, send its guarded command
            // translation as auxiliary info to GC.check
            if (cond.label == TagConstants.CHKOBJECTINVARIANT)
                code.addElement(GC.check(loc, cond, cond.pred));
            else
                code.addElement(GC.check(loc, cond));
        }
    }

    private static void checkModifiesConstraints(Spec spec,
                                                 FindContributors scope,
                                                 Set syntargets,
                                                 Hashtable premap,
                                                 int loc,
                                                 StackVector code) {
        // TBW
    }

    private static InvariantInfo mergeInvariants(InvariantInfo ii) {
        if( !Main.options().mergeInv )
            return ii;
    
        // Combined static/dynamic invariants, indexed by TypeSIg
        Hashtable staticInvs = new Hashtable();
        Hashtable dynInvs = new Hashtable();

        while( ii != null ) {

            Hashtable table = ii.isStatic ? staticInvs : dynInvs;

            InvariantInfo old = (InvariantInfo)table.get( ii.U );

            if( old == null ) {

                table.put( ii.U, ii );

            } else {

                // Add ii to old
                old.J = GC.and( old.J,
                                ii.isStatic ? ii.J
                                : GC.subst( ii.sdecl, old.s, ii.J ));
            }

            ii = ii.next;
        }

        // Now pull out merged invariants from tables
        Hashtable[] tables = { staticInvs, dynInvs };
        ii = null;

        for( int i=0; i<2; i++ ) {
            Hashtable table = tables[i];

            for( Enumeration e = table.elements(); e.hasMoreElements(); ) {
                InvariantInfo t = (InvariantInfo)e.nextElement();
                t.next = ii;
                ii = t;
            }
        }

        return ii;
    }

    private static boolean exprIsVisible(TypeSig originType, Expr e) {

        switch( e.getTag() ) {

            case TagConstants.FIELDACCESS:
                {
                    FieldAccess fa = (FieldAccess)e;
                    FieldDecl decl = fa.decl;

                    if( fa.od instanceof ExprObjectDesignator
                        && !exprIsVisible( originType,
                                           ((ExprObjectDesignator)fa.od).expr ) )
                        return false;

                    if( decl.parent == null ) {
                        // for array.length "field", there is no parent
                        return true;
                    } else if (Utils.findModifierPragma(decl,
                                                          TagConstants.SPEC_PUBLIC) != null) {
                        return true;
                    } else {
                        TypeSig sigDecl = TypeSig.getSig( decl.parent );
                        return TypeCheck.inst.canAccess( originType, sigDecl,
                                                         decl.modifiers,
                                                         decl.pmodifiers );
                    }
                }

            default:
                {
                    // Recurse over all children
                    for(int i=0; i<e.childCount(); i++ ) {
                        Object o = e.childAt(i);
                        if( o instanceof Expr ) {
                            if( !exprIsVisible(originType, (Expr)o) )
                                return false;
                        }
                    }

                    return true;
                }
        }
    }

    static public void collectFields(Expr e, java.util.Set s) {
// FIXME - have to avoid collecting bound variables of quantifiers
	switch (e.getTag()) {
	    case TagConstants.PRE:
		return;
	    case TagConstants.VARIABLEACCESS:
		VariableAccess va = (VariableAccess)e;
		if ( va.decl instanceof FormalParaDecl) {
			//System.out.println("PARA " + ((VariableAccess)e).decl );
			return;
		}
		if ( va.id.toString().endsWith("@pre")) return;
		//System.out.println("COLLECTED-VA " + e);
		s.add(e);
		break;
	    default:
	}

	// Recurse over all children
	for(int i=0; i<e.childCount(); i++ ) {
	    Object o = e.childAt(i);
	    if( o instanceof Expr ) collectFields((Expr)o,s);
	}


    }


    /***************************************************
     *                                                 *
     * Handling NON_NULL:			       *
     *                                                 *
     ***************************************************/


    /**
     ** Decorates <code>GenericVarDecl</code>'s to point to
     ** NonNullPragmas (SimpleModifierPragma's).
     **/
    //@ invariant nonnullDecoration != null;
    //@ invariant nonnullDecoration.decorationType == \type(SimpleModifierPragma);
    private static ASTDecoration nonnullDecoration
        = new ASTDecoration("nonnullDecoration");


    /**
     ** Mark v as non_null because of non_null pragma nonnull.
     **
     ** Precondition: nonnull is a NON_NULL pragma.
     **
     ** (Used to implement inheritence of non_null's.)
     **/
    private static void setNonNullPragma(GenericVarDecl v,
					 SimpleModifierPragma nonnull) {
	nonnullDecoration.set(v, nonnull);
    }


    /**
     ** Has a particular declaration been declared non_null?  If so,
     ** return the non_null pragma responsible.  Otherwise, return null.<p>
     **
     ** Precondition: if the declaration is a formal parameter, then the
     ** spec of it's routine has already been computed.<p>
     **
     **
     ** WARNING: this is the only authorized way to determine this
     ** information.  Do *not* attempt to search for NON_NULL modifiers
     ** directly.  (This is needed to handle inherited NON_NULL's
     ** properly.)
     **/
    public static SimpleModifierPragma NonNullPragma(GenericVarDecl v) {
	// First check for a mark:
/* In JML, non_null pragmas do not inherit!
	SimpleModifierPragma mark = (SimpleModifierPragma)
            nonnullDecoration.get(v);
	if (mark != null)
	    return mark;
*/

	// Else fall back on a direct search of local modifiers:
	return (SimpleModifierPragma)
            Utils.findModifierPragma(v, TagConstants.NON_NULL);
    }
    /** Returns non-null if the formal parameter is declared non-null in
	some overridden declaration of the method.
    */
    public static SimpleModifierPragma superNonNullPragma(GenericVarDecl v) {
	// First check for a mark:
	SimpleModifierPragma mark = (SimpleModifierPragma)
            nonnullDecoration.get(v);
	return mark;
    }

}


/**
 ** This class is used by <code>collectInvariants</code> and its callers,
 ** <code>extendSpecForCall</code> and <code>extendSpecForBody</code>.
 **/

class InvariantInfo {
    ExprDeclPragma prag;
    TypeSig U;           // "TypeSig" of class or interface that contains "prag"
    boolean isStatic;    // "true" if pragma declares a static invariant
    LocalVarDecl sdecl;  // "null" if "isStatic"; otherwise, a dummy variable
    VariableAccess s;    // "null" if "isStatic"; otherwise, a variable access
    // of "sdecl"
    Hashtable map;       // "{this-->s}"
    Expr J;              // translated expression, with substitution
    // "{this-->s}" if not "isStatic"
    InvariantInfo next;  // for linking "InvariantInfo" nodes
}

/** This class is used by <code>collectParamsAndGlobalVars</code> and its
 ** caller, <code>extendSpecForCall</code>.
 **/

class ParamAndGlobalVarInfo {
    GenericVarDecl vdecl;
    TypeSig U;
    boolean isNonnull;
    ParamAndGlobalVarInfo next;
}

