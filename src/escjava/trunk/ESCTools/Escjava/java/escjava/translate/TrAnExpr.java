/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.translate;

import java.util.Hashtable;
import java.util.Enumeration;
import java.util.LinkedList;

import javafe.ast.*;
import javafe.tc.*;
import javafe.util.Location;
import javafe.util.Assert;
import javafe.util.Info;
import javafe.util.Set;
import javafe.util.ErrorSet;
import escjava.ast.*;
import escjava.ast.TagConstants;
import escjava.ast.Modifiers;
import escjava.Main;
import escjava.tc.Types;
import escjava.parser.OldVarDecl;

/** Translates Annotation Expressions to GCExpr. */

public final class TrAnExpr {

    /** This hashtable keeps track of cautions issued, with respect to
     * using variables in \old pragmas that were not mentioned in modifies
     * pragmas.  The purpose of this hashtable is to prevent issuing
     * duplicate cautions.
     **/

    private static Set issuedPRECautions = new Set();  

    /** This is the abbreviated form of function <code>TrSpecExpr</code>
     * described in ESCJ 16.  It is a shorthand for the full form in which
     * <code>sp</code> and <code>st</code> are passed in as empty maps.
     **/

    public static Expr trSpecExpr(Expr e) {
        return trSpecExpr(e, null, null);
    }

    public static void initForClause() {
	trSpecExprAuxConditions = ExprVec.make();
	trSpecExprAuxAssumptions = ExprVec.make();
    }

    public static void initForRoutine() {
	trSpecExprAuxConditions = null;
	tempn = 100;
	declStack = new LinkedList();
	currentAlloc = GC.allocvar;
    }

    public static int level = 0;
    public static int maxLevel = 2; // FIXME if this is much bigger the JML specs file java.math.BigInteger.parse runs out of memory
    public static ExprVec trSpecExprAuxConditions = null;
    public static ExprVec trSpecExprAuxAssumptions = null;
    public static int tempn = 100;
    public static LinkedList declStack = new LinkedList();
    public static VariableAccess currentAlloc = GC.allocvar;

    /** This is the full form of function <code>TrSpecExpr</code>
     * described in ESCJ 16.  Each of the parameters <code>sp</code>
     * and <code>st</code> is allowed to be null, which is interpreted
     * as the empty map.
     **/

    public static Expr trSpecExpr(Expr e, Hashtable sp, Hashtable st) {
        int tag = e.getTag();
        switch (tag) {
        case TagConstants.THISEXPR: {
            ThisExpr t = (ThisExpr)e;
            if (t.classPrefix!=null)
                return trSpecExpr(Inner.unfoldThis(t), sp, st);

            return apply(sp, makeVarAccess(GC.thisvar.decl, e.getStartLoc()));
        }

        // Literals (which are already GCExpr's
        case TagConstants.BOOLEANLIT: 
        case TagConstants.STRINGLIT:
        case TagConstants.CHARLIT:
        case TagConstants.DOUBLELIT: 
        case TagConstants.FLOATLIT:
        case TagConstants.INTLIT:
        case TagConstants.LONGLIT:
        case TagConstants.NULLLIT:
            return e;
      
        case TagConstants.RESEXPR:
            return apply(sp, makeVarAccess(GC.resultvar.decl, e.getStartLoc()));

        case TagConstants.LOCKSETEXPR:
            return apply(sp, makeVarAccess(GC.LSvar.decl, e.getStartLoc()));

        case TagConstants.VARIABLEACCESS: {
            VariableAccess va = (VariableAccess)e;
	    if (va.decl instanceof OldVarDecl) {
		// variable declared in an old pragma (not the \old fcn.)
		VarInit vi = ((OldVarDecl)va.decl).init;
		if (vi instanceof Expr) {
		    return trSpecExpr( (Expr)vi, sp, st);
		} else {
		    ErrorSet.fatal(e.getStartLoc(),
			"Have not implemented array initializers in old annotations");
		}
	    } else {
		// local variable, parameter, or bound variable
		return apply(sp, va);
	    }
        }

        case TagConstants.FIELDACCESS: {
            FieldAccess fa = (FieldAccess)e;
            VariableAccess va = makeVarAccess(fa.decl, fa.locId);
            // va accesses the field
	    if (GetSpec.findModifierPragma(va.decl.pmodifiers,TagConstants.MODEL) != null) {
		java.util.List reps = escjava.AnnotationHandler.findRepresents(fa.decl);
		java.util.Iterator it = reps.iterator();
		while (it.hasNext()) {
		    Expr ex = (Expr)it.next();
	
		    if (trSpecExprAuxConditions != null && !declStack.contains(fa.decl)) {
			declStack.addFirst(fa.decl);

			Hashtable h = new Hashtable();
			if (fa.od instanceof ExprObjectDesignator) {
			    if (!(((ExprObjectDesignator)fa.od).expr instanceof ThisExpr)) {
				h.put(Substitute.thisexpr, ((ExprObjectDesignator)fa.od).expr);
			    }
			} else if (fa.od instanceof SuperObjectDesignator) {
				// FIXME
			    System.out.println("NOT SUPPORTED " + fa.od.getClass());
			} // fall-through for TypeObjectDesignator
			    
			ex = Substitute.doSubst(h,ex);
			Expr ee = trSpecExpr(ex,sp,st);
			trSpecExprAuxConditions.addElement(ee);
			declStack.removeFirst();
		    }
		}
	    }

            if (Modifiers.isStatic(fa.decl.modifiers)) {
		//fa.od.getTag() == TagConstants.TYPEOBJECTDESIGNATOR) {
		VariableAccess nva = apply(sp, va);
                return nva;
            } else {
                // select expression whose rhs is an instance variable
                Expr lhs;
                switch (fa.od.getTag()) {
                case TagConstants.EXPROBJECTDESIGNATOR: {
                    ExprObjectDesignator eod = (ExprObjectDesignator)fa.od;
                    lhs = trSpecExpr(eod.expr, sp, st);
                    break;
                }

                case TagConstants.SUPEROBJECTDESIGNATOR:
                    lhs = apply(sp, makeVarAccess(GC.thisvar.decl,
                                                  fa.od.getStartLoc()));
                    break;
		
                default:
                    //@ unreachable
                    Assert.fail("Fall thru; tag = "
                                + escjava.ast.TagConstants.toString(fa.od.getTag()));
                    lhs = null; // dummy assignment
                }
	    
                if (fa.decl == Types.lengthFieldDecl)
                    return GC.nary(fa.getStartLoc(), fa.getEndLoc(),
                                   TagConstants.ARRAYLENGTH, lhs);
                else
                    return GC.nary(fa.getStartLoc(), fa.getEndLoc(),
                                   TagConstants.SELECT, apply(sp, va), lhs);
            }
        }

        case TagConstants.ARRAYREFEXPR: {
            ArrayRefExpr r = (ArrayRefExpr)e;

            if (TypeCheck.inst.getType(r.array).getTag() == TagConstants.LOCKSET) {
                return GC.nary(r.array.getStartLoc(), r.locCloseBracket,
                               TagConstants.SELECT,
                               trSpecExpr(r.array, sp, st),
                               trSpecExpr(r.index, sp, st));
            } else {
                VariableAccess elems = apply(sp, makeVarAccess(GC.elemsvar.decl,
                                                               e.getStartLoc()));
                Expr e0 = trSpecExpr(r.array, sp, st);
                Expr e1 = trSpecExpr(r.index, sp, st);
                Expr a = GC.nary(TagConstants.SELECT, elems, e0);
                return GC.nary(r.array.getStartLoc(), r.locCloseBracket,
                               TagConstants.SELECT, a, e1);
            }
        }

        case TagConstants.WILDREFEXPR: {
            WildRefExpr r = (WildRefExpr)e;

            VariableAccess elems = apply(sp, makeVarAccess(GC.elemsvar.decl,
                                                           e.getStartLoc()));
	Expr arr = trSpecExpr(r.expr, sp, st);
	return GC.nary(e.getStartLoc(), r.locCloseBracket,
		       TagConstants.SELECT, elems, arr);
      }

      case TagConstants.PARENEXPR: {
	// drop parens
        ParenExpr pe = (ParenExpr)e;
	return trSpecExpr(pe.expr, sp, st);
      }

      // Unary operator expressions
      
      case TagConstants.UNARYSUB: 
      case TagConstants.NOT: 
      case TagConstants.BITNOT: {
	UnaryExpr ue = (UnaryExpr)e;
	int newtag = getGCTagForUnary(ue);
	return GC.nary(ue.getStartLoc(), ue.getEndLoc(), newtag, 
		       trSpecExpr(ue.expr, sp, st));
      }

      case TagConstants.UNARYADD: {
	// drop UnaryADD
	UnaryExpr ue = (UnaryExpr)e;
	return trSpecExpr(ue.expr, sp, st);
      }

      case TagConstants.TYPEOF:
      case TagConstants.ELEMTYPE:
      case TagConstants.MAX:
	Assert.notFalse(((NaryExpr)e).exprs.size() == 1);
	// fall through
      case TagConstants.DTTFSA: {
	NaryExpr ne = (NaryExpr)e;
	ExprVec exprs = ExprVec.make(ne.exprs.size());
	for (int i = 0; i < ne.exprs.size(); i++) {
	  exprs.addElement(trSpecExpr(ne.exprs.elementAt(i), sp, st));
	}
	return GC.nary(ne.getStartLoc(), ne.getEndLoc(), ne.getTag(), exprs);
      }

      case TagConstants.ELEMSNONNULL: {
	NaryExpr ne = (NaryExpr)e;
	VariableAccess elems = apply(sp, makeVarAccess(GC.elemsvar.decl,
						       e.getStartLoc()));

	return GC.nary(ne.getStartLoc(), ne.getEndLoc(), ne.getTag(),
		       trSpecExpr(ne.exprs.elementAt(0), sp, st), elems);
      }

      // Binary operator expressions
      
      case TagConstants.OR:
      case TagConstants.AND:
      case TagConstants.BITOR:
      case TagConstants.BITAND:
      case TagConstants.BITXOR:
      case TagConstants.EQ:
      case TagConstants.NE:
      case TagConstants.GE:
      case TagConstants.GT:
      case TagConstants.LE:
      case TagConstants.LT:
      case TagConstants.LSHIFT:
      case TagConstants.RSHIFT:
      case TagConstants.URSHIFT:
      case TagConstants.ADD:
      case TagConstants.SUB:
      case TagConstants.DIV:
      case TagConstants.MOD:
      case TagConstants.STAR:
      case TagConstants.IMPLIES:
      case TagConstants.IFF:
      case TagConstants.NIFF: {
        BinaryExpr be = (BinaryExpr)e;
	int newtag = getGCTagForBinary(be);
	return GC.nary(be.getStartLoc(), be.getEndLoc(),
		       newtag,
		       trSpecExpr(be.left, sp, st),
		       trSpecExpr(be.right, sp, st));
      }

      case TagConstants.NEWINSTANCEEXPR: {
	NewInstanceExpr me = (NewInstanceExpr)e;
	Type type = TypeCheck.inst.getType(me);
	Identifier n = Identifier.intern("tempNewObject"+(++tempn));
	VariableAccess v =  VariableAccess.make(n, e.getStartLoc(), 
			LocalVarDecl.make(Modifiers.NONE, null,n,
				type,
				UniqName.temporaryVariable,
				null, Location.NULL));
	if (trSpecExprAuxConditions == null || level > maxLevel
		|| declStack.contains(me.decl)) {
	    return v;
	}
//System.out.println("NEWINST " + Location.toString(me.decl.getStartLoc()) + " " + declStack.contains(me.decl));
	++level;
	declStack.addFirst(me.decl);
	if (false) { // FIXME - do this if a functional constructor
	    ExprVec ev = ExprVec.make(me.args.size());
		    // FIXME - 'this' argument???
		    // FIXME - enclosingInstance ???
	    for (int i=0; i<me.args.size(); ++i) {
		ev.addElement( trSpecExpr( me.args.elementAt(i), sp, st));
	    }
	    Expr ne = GC.nary(me.getStartLoc(), me.getEndLoc(),
			    TagConstants.METHODCALL,ev);
	    ((NaryExpr)ne).methodName = Identifier.intern(
		    "new#" + me.args.size() + "#" + me.type.name.printName());
		    // FIXME - does the name need to be unique across signatures?
	    Expr ee = GC.nary(TagConstants.ANYEQ, v, ne);
	    // FIXME - should add the following mapping of the temp variable
	    // to the method only if the method is a function call - pure
	    // method of immutable objects, and either static or has the
	    // this object inserted as an argument.
	    trSpecExprAuxConditions.addElement(ee);
	}
	Expr ee = GC.nary(TagConstants.REFNE, v, 
	    LiteralExpr.make(TagConstants.NULLLIT, null, Location.NULL));
	trSpecExprAuxConditions.addElement(ee);
	ee = GC.nary(TagConstants.TYPEEQ,
	    GC.nary(TagConstants.TYPEOF, v),
	    TypeExpr.make(Location.NULL, Location.NULL, type));
	trSpecExprAuxConditions.addElement(ee);
	VariableAccess newAlloc =
	    apply(sp,GC.makeVar(GC.allocvar.id,e.getStartLoc())); // alloc
	trSpecExprAuxAssumptions.addElement(
	    GC.nary(TagConstants.ALLOCLT, currentAlloc, newAlloc));
	trSpecExprAuxConditions.addElement(
	    GC.nary(TagConstants.BOOLNOT,
		GC.nary(TagConstants.ISALLOCATED, v, currentAlloc)));
	trSpecExprAuxConditions.addElement(
	    GC.nary(TagConstants.ISALLOCATED, v, newAlloc));
	currentAlloc = newAlloc;
	getCalledSpecs(me.decl,null,me.args,v,sp,st); // adds to trSpecExprAuxConditions
//System.out.println("END-NEWINST " + Location.toString(me.decl.getStartLoc()) + " " + declStack.contains(me.decl));
	declStack.removeFirst();
	--level;
	return v;
		// FIXME could allow for functional constructors
      }

      case TagConstants.METHODINVOCATION: {
	
	MethodInvocation me = (MethodInvocation)e;

	boolean isFunction = (GetSpec.findModifierPragma(me.decl.pmodifiers,TagConstants.FUNCTION) != null);

	Identifier n = Identifier.intern("tempMethodReturn"+(++tempn));
	VariableAccess v =  VariableAccess.make(n, e.getStartLoc(), 
			LocalVarDecl.make(Modifiers.NONE, null,n,
				TypeCheck.inst.getType(me),
				UniqName.temporaryVariable,
				null, Location.NULL));
	if (trSpecExprAuxConditions == null || level > maxLevel 
		|| declStack.contains(me.decl)) {
	    if (!isFunction) return v;
	    ExprVec ev = ExprVec.make(me.args.size());
		    // FIXME - 'this' argument???
	    for (int i=0; i<me.args.size(); ++i) {
		ev.addElement( trSpecExpr( me.args.elementAt(i), sp, st));
	    }
	    Expr ne = GC.nary(me.getStartLoc(), me.getEndLoc(),
			    TagConstants.METHODCALL,ev);
	    ((NaryExpr)ne).methodName = 
		    Identifier.intern(me.id.toString() + "." + me.args.size()); // FIXME -- full name ??? with type signature as well
	    return ne;
	}
//for (int ind=0; ind<level; ++ind) System.out.print(" " ); System.out.println("METHINV " + Location.toString(me.decl.getStartLoc()) + " " + declStack.contains(me.decl));

	++level;
	declStack.addFirst(me.decl);

	if (isFunction) {
	    ExprVec ev = ExprVec.make(me.args.size());
		    // FIXME - 'this' argument???
	    for (int i=0; i<me.args.size(); ++i) {
		ev.addElement( trSpecExpr( me.args.elementAt(i), sp, st));
	    }
	    Expr ne = GC.nary(me.getStartLoc(), me.getEndLoc(),
			    TagConstants.METHODCALL,ev);
	    ((NaryExpr)ne).methodName = 
		    Identifier.intern(me.id.toString() + "." + me.args.size()); // FIXME -- full name ??? with type signature as well
	    Expr ee = GC.nary(TagConstants.ANYEQ, v, ne);
	    trSpecExprAuxConditions.addElement(ee);
	}

	getCalledSpecs(me.decl,me.od,me.args,v,sp,st); // adds to trSpecExprAuxConditions
	--level;
//for (int ind=0; ind<level; ++ind) System.out.print(" " ); System.out.println("END-METHINV " + Location.toString(me.decl.getStartLoc()) + " " + declStack.contains(me.decl));
	declStack.removeFirst();
	return v;

      }

      case TagConstants.NEWARRAYEXPR: {
	NewArrayExpr nae = (NewArrayExpr)e;
// FIXME - need to put in the type and the dimension array
// also need to make SImplify understand the make$Array function
	if (trSpecExprAuxConditions != null ) {
	    Identifier n = Identifier.intern("tempMethodReturn"+(++tempn));
	    VariableAccess v =  VariableAccess.make(n, e.getStartLoc(), 
			    LocalVarDecl.make(Modifiers.NONE, null,n,
				    TypeCheck.inst.getType(nae),
				    UniqName.temporaryVariable,
				    null, Location.NULL));

	    ExprVec ev = ExprVec.make(7);
	    ev.addElement( v ); // variable name
	    ev.addElement(apply(sp,currentAlloc) ); // alloc
	    VariableAccess newAlloc = GC.makeVar(GC.allocvar.id,nae.getStartLoc());
	    ev.addElement(apply(sp,newAlloc) ); // alloc
	    trSpecExprAuxAssumptions.addElement(
		GC.nary(TagConstants.ALLOCLT, currentAlloc, newAlloc));
	    currentAlloc = newAlloc;
	    ev.addElement(GC.elemsvar ); // elems
	    Expr edims = GC.nary( TagConstants.ARRAYSHAPEONE, 
				trSpecExpr( nae.dims.elementAt(0), sp, st));
	    for (int kk = 1; kk < nae.dims.size(); ++kk) {
		edims = GC.nary( TagConstants.ARRAYSHAPEMORE,
				trSpecExpr( nae.dims.elementAt(kk), sp, st));
	    }
	    ev.addElement(edims ); // arrayShape
	    ev.addElement( TypeExpr.make(Location.NULL, Location.NULL, TypeCheck.inst.getType(nae)) );
	    if (Types.isIntType(nae.type))
		ev.addElement( LiteralExpr.make(TagConstants.INTLIT, new Integer(0), Location.NULL)); // initial value
	    else if (Types.isReferenceType(nae.type))
		ev.addElement( LiteralExpr.make(TagConstants.NULLLIT, null, Location.NULL));

	    trSpecExprAuxConditions.addElement(GC.nary(TagConstants.ARRAYFRESH,ev));
	    return v;
		// FIXME for multiple dimensions
	} else {
	    ErrorSet.notImplemented(!Main.options().noNotCheckedWarnings,
		e.getStartLoc(),"Not checking predicates containing new array expressions");
	    return null;
	}
      }

      case TagConstants.EXPLIES: {
	// handle as implies, but with arguments reversed
        BinaryExpr be = (BinaryExpr)e;
	return GC.nary(be.getStartLoc(), be.getEndLoc(),
		       TagConstants.BOOLIMPLIES,
		       trSpecExpr(be.right, sp, st),
		       trSpecExpr(be.left, sp, st));
      }

      case TagConstants.SUBTYPE: {
	BinaryExpr be = (BinaryExpr)e;
	return GC.nary(be.getStartLoc(), be.getEndLoc(),
		       TagConstants.TYPELE,
		       trSpecExpr(be.left, sp, st),
		       trSpecExpr(be.right, sp, st));
      }

      // Other expressions

      case TagConstants.CONDEXPR: {
        CondExpr ce = (CondExpr)e;
        return GC.nary(ce.test.getStartLoc(), ce.test.getEndLoc(),
		       TagConstants.CONDITIONAL,
		       trSpecExpr(ce.test, sp, st),
		       trSpecExpr(ce.thn, sp, st),
		       trSpecExpr(ce.els, sp, st));
      }

      case TagConstants.INSTANCEOFEXPR: {
        InstanceOfExpr ie = (InstanceOfExpr)e;
	Expr isOfType = GC.nary(ie.getStartLoc(), ie.getEndLoc(), 
			 TagConstants.IS,
		         trSpecExpr(ie.expr, sp, st),
			 trType(ie.type));
	Expr notNull = GC.nary(ie.getStartLoc(), ie.getEndLoc(), 
			 TagConstants.REFNE,
		         trSpecExpr(ie.expr, sp, st),
			 GC.nulllit);

        return GC.and(ie.getStartLoc(), ie.getEndLoc(),
		       isOfType,
		       notNull);
      }

      case TagConstants.CASTEXPR: {
        CastExpr ce = (CastExpr)e;
        return GC.nary(ce.getStartLoc(), ce.getEndLoc(), TagConstants.CAST,
		       trSpecExpr(ce.expr, sp, st),
		       trType(ce.type));
      }

      case TagConstants.CLASSLITERAL: {
        ClassLiteral cl = (ClassLiteral)e;
        return GC.nary(cl.getStartLoc(), cl.getEndLoc(),
		       TagConstants.CLASSLITERALFUNC,
		       trType(cl.type));
      }

      case TagConstants.TYPEEXPR:
	return e;

      case TagConstants.REACH: {
	    ErrorSet.notImplemented(!Main.options().noNotCheckedWarnings,
		e.getStartLoc(),"Not checking predicates containing reach expressions");
	    // FIXME - ignore these till we can figure out how to reason
	    return null;
        }

      case TagConstants.NUM_OF:
      case TagConstants.MIN:
      case TagConstants.MAXQUANT:
      case TagConstants.SUM:
      case TagConstants.PRODUCT:
	{
	    //ErrorSet.notImplemented(!Main.options().noNotCheckedWarnings,
		//e.getStartLoc(),"Not checking predicates containing generalized quantifier expressions");
	    // FIXME - ignore these till we can figure out how to reason
		// Not sure this is the correct type ??? FIXME
	    Type t = TypeCheck.inst.getType(e);
	    return tempName(e.getStartLoc(),"quantvalue",t);
        }

      case TagConstants.FORALL:
      case TagConstants.EXISTS: {
	  QuantifiedExpr qe = (QuantifiedExpr)e;
	if (qe.vars.size() != 1) {
	  int locStart = e.getStartLoc();
	  int locEnd = e.getEndLoc();

	  Expr goodTypes = GC.truelit;
	  Expr body = trSpecExpr(qe.expr, sp, st);
	  return GC.quantifiedExpr(locStart, locEnd, tag,
				   qe.vars, body, null);
	} else if (Main.options().nestQuantifiers) {
	  GenericVarDecl decl = qe.vars.elementAt(0);

	  Assert.notFalse(sp == null || ! sp.contains(decl));
	  Assert.notFalse(st == null || ! st.contains(decl));
	  Assert.notFalse( qe.vars.size() == 1 );

	  int op;
	  if (qe.getTag() == TagConstants.FORALL)
	    op = TagConstants.BOOLIMPLIES;
	  else
	    op = TagConstants.BOOLAND;

	  Expr body = GC.nary(qe.getStartLoc(), qe.getEndLoc(), op,
			      quantTypeCorrect(decl, sp),
			      trSpecExpr(qe.expr, sp, st));
	  return GC.quantifiedExpr(qe.getStartLoc(), qe.getEndLoc(),
				   qe.getTag(),
				   decl, body, null);
	} else {
	  int locStart = e.getStartLoc();
	  int locEnd = e.getEndLoc();

	  int op;
	  if (tag == TagConstants.FORALL)
	    op = TagConstants.BOOLIMPLIES;
	  else
	    op = TagConstants.BOOLAND;

	  GenericVarDeclVec dummyDecls = GenericVarDeclVec.make();
	  Expr goodTypes = GC.truelit;
	  while (true) {
	    for (int k=0; k<qe.vars.size(); ++k) {
		GenericVarDecl decl = qe.vars.elementAt(k);
		Assert.notFalse(sp == null || ! sp.contains(decl));
		Assert.notFalse(st == null || ! st.contains(decl));
		dummyDecls.addElement(decl);

		goodTypes = GC.and(goodTypes, quantTypeCorrect(decl, sp));
	    }
	    if (qe.expr.getTag() == tag) {
	      qe = (QuantifiedExpr)qe.expr;
	    } else {
	      Expr body = trSpecExpr(qe.expr, sp, st);
	      Expr qbody = GC.nary(locStart, locEnd, op, goodTypes, body);
	      return GC.quantifiedExpr(locStart, locEnd, tag,
				       dummyDecls, qbody, null);
	    }
	  }
	}
	//@ unreachable
      }

      case TagConstants.SETCOMPEXPR: {
	ErrorSet.notImplemented(!Main.options().noNotCheckedWarnings,
		e.getStartLoc(),"Not checking predicates containing set comprehension expressions");
	return null;
      }

      case TagConstants.LABELEXPR: {
	LabelExpr le = (LabelExpr)e;
	return LabelExpr.make(le.getStartLoc(), le.getEndLoc(),
			      le.positive, le.label,
			      trSpecExpr(le.expr, sp, st));
      }

      case TagConstants.PRE: {
	  //
	  // Original code altered to generate a caution if the variables in
	  // the PRE clause are not mentioned in an appropriate "modifies"
	  // clause.  Caroline Tice, 1/11/2000
	  // Note: Current implementation assumes that if ANY substitution 
	  //       takes place, then ALL appropriate substitutions took place.

	  NaryExpr ne = (NaryExpr)e;

	  /*  Compare the number of substituted variables before and
	   *  after translating the PRE expression, using only the st
	   *  list (i.e. the "modifies" list) for the translations.  If
	   *  no substitutions took place, generate a caution.
	   *  Then translate the expression previously generated, using
	   *  the union of sp and st.
	   */

/* FIXME - disable this for now.  We use \old in AnnotationHandler when we
are desugaring annotations, to wrap around a requires predicate when it is
being combined with an ensures predicate.  This error would have us only
wrap those variables being modified and not everything.
	  int cReplacementsBefore = getReplacementCount();
	  Expr tmpExpr = trSpecExpr(ne.exprs.elementAt(0), st, null);
	  if (cReplacementsBefore == getReplacementCount()) {
	      int loc = ne.getStartLoc();
	      String locStr = Location.toString(loc).intern();
	      if (!(issuedPRECautions.contains(locStr))) {
		  ErrorSet.caution (loc, 
		      "Variables in \\old not mentioned in modifies pragma.");
		  issuedPRECautions.add(locStr);
	      }
	  }
	  //return trSpecExpr(ne.exprs.elementAt(0), union(sp, st), null);
*/
	if (st != null) {
	    return trSpecExpr(ne.exprs.elementAt(0), st, null);
	} else {
	    return trSpecExpr(ne.exprs.elementAt(0), sp, st);
	}
      }

      case TagConstants.FRESH: {
	NaryExpr ne = (NaryExpr)e;
	int sloc = ne.getStartLoc();
	int eloc = ne.getEndLoc();
	Expr arg = trSpecExpr(ne.exprs.elementAt(0), sp, st);
	// arg != null
	Expr nonnull = GC.nary(sloc, eloc,
			       TagConstants.REFNE, arg, GC.nulllit);
	// isAllocated(arg, alloc@pre)
	Expr isAlloced = GC.nary(sloc, eloc, TagConstants.ISALLOCATED,
				 arg, apply(st, GC.allocvar));
	// !isAllocated(arg, alloc@pre)
	Expr newlyallocated = GC.not(sloc, eloc, isAlloced);
	return GC.and(sloc, eloc, nonnull, newlyallocated);
      }

      case TagConstants.DOTDOT:
	BinaryExpr be = (BinaryExpr)e;
// FIXME
	return be.left;

      case TagConstants.NOWARN_OP:
      case TagConstants.WACK_NOWARN:
      case TagConstants.WARN_OP:
      case TagConstants.WARN:
      {
	// FIXME - set these as a pass through for now
	NaryExpr ne = (NaryExpr)e;
	return trSpecExpr(ne.exprs.elementAt(0), sp, st);
      }

      case TagConstants.IS_INITIALIZED:
      case TagConstants.INVARIANT_FOR:{
	// We return a fresh temporary variable, unused elsewhere, until
	// we know how to determine some conditions that these functions
	// satisfy.  FIXME
	Identifier n = Identifier.intern("tempInit"+(++tempn));
	VariableAccess v =  VariableAccess.make(n, e.getStartLoc(), 
			LocalVarDecl.make(Modifiers.NONE, null,n,
				Types.booleanType,
				UniqName.temporaryVariable,
				null, Location.NULL));
	return v;
      } 

      case TagConstants.SPACE:
      case TagConstants.WACK_WORKING_SPACE:
      case TagConstants.WACK_DURATION: {
	// We return a fresh temporary variable, unused elsewhere, until
	// we know how to determine some conditions that these functions
	// satisfy.  FIXME
	return tempName(e.getStartLoc(),"tempResources",Types.longType);
      }

      case TagConstants.NOTHINGEXPR:
	return null;

      case TagConstants.NOTMODIFIEDEXPR: {
	Expr ee = ((NotModifiedExpr)e).expr;
	Expr post = trSpecExpr(ee,sp,st);
	Expr pre;
	if (st == null) {
	    pre = trSpecExpr(ee,sp,st);
	} else {
	    pre = trSpecExpr(ee,st,null);
	}
	return LabelExpr.make(ee.getStartLoc(),ee.getEndLoc(),
		false,GC.makeLabel("AdditionalInfo",ee.getStartLoc(),Location.NULL),GC.nary(TagConstants.ANYEQ,post,pre));
      }

      default:
	Assert.fail("UnknownTag<"+e.getTag()+","+
		    TagConstants.toString(e.getTag())+"> on "+e+ " " +
		    Location.toString(e.getStartLoc()));
	return null; // dummy return
    }
  }

  static VariableAccess tempName(int loc, String prefix, Type type) {
	Identifier n = Identifier.intern(prefix + (++tempn));
	VariableAccess v =  VariableAccess.make(n, loc, 
			LocalVarDecl.make(Modifiers.NONE, null,n,
				type,
				UniqName.temporaryVariable,
				null, Location.NULL));
	return v;
  }

  static Hashtable union(Hashtable h0, Hashtable h1) {
    if (h0 == null)
      return h1;
    if (h1 == null)
      return h0;
    Hashtable h2 = new Hashtable();
    for (Enumeration enum = h0.keys(); enum.hasMoreElements(); ) {
      Object key = enum.nextElement();
      h2.put(key, h0.get(key));
    }
    for (Enumeration enum = h1.keys(); enum.hasMoreElements(); ) {
      Object key = enum.nextElement();
      h2.put(key, h1.get(key));
    }
    return h2;
  }
  
  /** This method implements the ESCJ 16 function
    * <code>TargetTypeCorrect</code>,
    *
    *      except for the <code>init$</code> case!
    *
    **/

  /*@ requires vd == GC.allocvar.decl ==> wt != null */
  public static Expr targetTypeCorrect(/*@ non_null */ GenericVarDecl vd,
				       Hashtable wt) {
    if (vd == GC.elemsvar.decl) {
      // ElemsTypeCorrect[[ vd ]]
      return elemsTypeCorrect(vd);
    } else if (vd == GC.allocvar.decl) {
      // wt[[ alloc ]] < alloc
      VariableAccess allocPre = (VariableAccess)wt.get(GC.allocvar.decl);
      return GC.nary(TagConstants.ALLOCLT, allocPre, GC.allocvar);
    } else if (vd instanceof FieldDecl && !Modifiers.isStatic(vd.modifiers)) {
      // FieldTypeCorrect[[ vd ]]
      return fieldTypeCorrect((FieldDecl)vd);
    } else {
      // TBW:  If we ever implement safe loops, we need a case for
      // "init$" here, see ESCJ 16.
      
      // TypeCorrect[[ vd ]]
      return typeCorrect(vd);
    }
  }

  /** This method implements the ESCJ 16 function <code>TypeCorrect</code>.
    **/

  public static Expr typeCorrect(GenericVarDecl vd) {
    return typeAndNonNullCorrectAs(vd, vd.type,
				   GetSpec.NonNullPragma(vd), false,
				   null);
  }

  public static Expr typeCorrect(GenericVarDecl vd, Hashtable sp) {
    return typeAndNonNullCorrectAs(vd, vd.type,
				   GetSpec.NonNullPragma(vd), false,
				   sp);
  }

  // "vd" is a quantified variable
  public static Expr quantTypeCorrect(GenericVarDecl vd, Hashtable sp) {
    Assert.notFalse(GetSpec.NonNullPragma(vd) == null);
    if ((Types.isIntType(vd.type) || Types.isLongType(vd.type)) &&
	!Main.options().useIntQuantAntecedents) {
      return GC.truelit;
    } else {
      return typeAndNonNullCorrectAs(vd, vd.type, null, true, sp);
    }
  }

  public static Expr typeCorrectAs(GenericVarDecl vd, Type type) {
    return typeAndNonNullCorrectAs(vd, type, null, false, null);
  }
  
  public static Expr typeAndNonNullCorrectAs(GenericVarDecl vd,
					     Type type,
					     SimpleModifierPragma nonNullPragma,
					     boolean forceNonNull,
					     Hashtable sp) {
    return GC.and(typeAndNonNullAllocCorrectAs(vd, type,
					       nonNullPragma, forceNonNull,
					       sp, true));
  }

  /** Returns a vector of conjuncts.  This vector is "virgin" and can be modified
    * by the caller.  It contains at least 2 empty slots, allows clients to
    * append a couple of items without incurring another allocation.
    */
  
  public static ExprVec typeAndNonNullAllocCorrectAs(GenericVarDecl vd,
						     Type type,
						     SimpleModifierPragma nonNullPragma,
						     boolean forceNonNull,
						     Hashtable sp,
						     boolean mentionAllocated) {
    VariableAccess v = makeVarAccess(vd, Location.NULL);
    ExprVec conjuncts = ExprVec.make(5);

    // is(v, type)
    Expr e = GC.nary(TagConstants.IS, v, trType(type));
    conjuncts.addElement(e);
    if (! Types.isReferenceType(type))
      return conjuncts;

    if (mentionAllocated) {
      // isAllocated(v, alloc)
      e = GC.nary(TagConstants.ISALLOCATED,
		  v,
		  apply(sp, GC.allocvar));
      conjuncts.addElement(e);
    }

    if (nonNullPragma != null || forceNonNull) {
      e = GC.nary(TagConstants.REFNE, v, GC.nulllit);
      if (nonNullPragma != null) {
	int locPragmaDecl = nonNullPragma.getStartLoc();
        if (Main.options().guardedVC && locPragmaDecl != Location.NULL) {
          e = GuardExpr.make(e, locPragmaDecl);
        }
	LabelInfoToString.recordAnnotationAssumption(locPragmaDecl);
      }
      conjuncts.addElement(e);
    }

    return conjuncts;
  }

  public static Expr fieldTypeCorrect(FieldDecl fdecl) {
    VariableAccess f = makeVarAccess(fdecl, Location.NULL);

    // f == asField(f, T)
    Expr asField = GC.nary(TagConstants.ANYEQ,
			   f,
			   GC.nary(TagConstants.ASFIELD,
				   f,
				   trType(fdecl.type)));
    if (! Types.isReferenceType(fdecl.type))
      return asField;

    ExprVec conjuncts = ExprVec.make(3);
    conjuncts.addElement(asField);
    
    // fClosedTime(f) < alloc
    {
      Expr c0 = GC.nary(TagConstants.ALLOCLT,
			GC.nary(TagConstants.FCLOSEDTIME, f),
			GC.allocvar);
      conjuncts.addElement(c0);
    }

    SimpleModifierPragma nonNullPragma = GetSpec.NonNullPragma(fdecl);
    if (nonNullPragma != null) {
      // (ALL s :: s != null ==> f[s] != null)
      LocalVarDecl sDecl = UniqName.newBoundVariable('s');
      VariableAccess s = makeVarAccess(sDecl, Location.NULL);
      Expr c0 = GC.nary(TagConstants.REFNE, s, GC.nulllit);
      Expr c1 = GC.nary(TagConstants.REFNE, GC.select(f, s), GC.nulllit);
      Expr quant = GC.forall(sDecl, GC.implies(c0, c1));
      int locPragmaDecl = nonNullPragma.getStartLoc();
      LabelInfoToString.recordAnnotationAssumption(locPragmaDecl);
      if (Main.options().guardedVC && locPragmaDecl != Location.NULL) {
        quant = GuardExpr.make(quant, locPragmaDecl);
      }
      conjuncts.addElement(quant);
    }
    
    return GC.and(conjuncts);
  }
  
  public static Expr elemsTypeCorrect(GenericVarDecl edecl) {
    VariableAccess e = makeVarAccess(edecl, Location.NULL);
    // c0:  e == asElems(e)
    Expr c0 = GC.nary(TagConstants.ANYEQ, e, GC.nary(TagConstants.ASELEMS, e));
    // c1:  eClosedTime(e) < alloc
    Expr c1 = GC.nary(TagConstants.ALLOCLT,
		      GC.nary(TagConstants.ECLOSEDTIME, e),
		      GC.allocvar);
    // c0 && c1
    return GC.and(c0, c1);
  }
  
  /* getGCTagForBinary uses a 2-dim lookup table.  Each entry is:

   *<PRE>
   * { Binary tag,
   *     nary-tag-for-bool, nary-tag-for-integral, nary-tag-for-long-integral,
   *     nary-tag-for-floats, nary-tag-for-refs, nary-tag-for-typecode
   * }.
   * In the nary-tag-for-long-integral column, a -1 means unused.
   * In other columns, -1 means invalid combination.
   * </PRE>
   * */
  
  private static final int binary_table[][] 
  = { { TagConstants.OR,
	    TagConstants.BOOLOR, -1, -1,
            -1, -1, -1 },
      { TagConstants.AND,
            TagConstants.BOOLAND, -1, -1,
            -1, -1, -1 },
      { TagConstants.IMPLIES,
	    TagConstants.BOOLIMPLIES, -1, -1,
            -1, -1, -1 },
      { TagConstants.IFF,
	    TagConstants.BOOLEQ, -1, -1,
            -1, -1, -1 },
      { TagConstants.NIFF,
	    TagConstants.BOOLNE, -1, -1,
            -1, -1, -1 },
      { TagConstants.BITOR,
	    TagConstants.BOOLOR, TagConstants.INTEGRALOR, -1,
            -1, -1, -1 },
      { TagConstants.ASGBITOR,
	    TagConstants.BOOLOR, TagConstants.INTEGRALOR, -1,
            -1, -1, -1 },
      { TagConstants.BITAND,
	    TagConstants.BOOLAND, TagConstants.INTEGRALAND, -1,
            -1, -1, -1 },
      { TagConstants.ASGBITAND,
	    TagConstants.BOOLAND, TagConstants.INTEGRALAND, -1,
            -1, -1, -1 },
      { TagConstants.BITXOR,
	    TagConstants.BOOLNE, TagConstants.INTEGRALXOR, -1,
            -1, -1, -1 },
      { TagConstants.ASGBITXOR,
	    TagConstants.BOOLNE, TagConstants.INTEGRALXOR, -1,
            -1, -1, -1 },
      { TagConstants.EQ,
	    TagConstants.BOOLEQ, TagConstants.INTEGRALEQ, -1,
	    TagConstants.FLOATINGEQ, TagConstants.REFEQ, TagConstants.TYPEEQ },
      { TagConstants.NE,
	    TagConstants.BOOLNE, TagConstants.INTEGRALNE, -1,
	    TagConstants.FLOATINGNE, TagConstants.REFNE,  TagConstants.TYPENE },
      { TagConstants.GE,
            -1, TagConstants.INTEGRALGE, -1,
	    TagConstants.FLOATINGGE, -1, -1 },
      { TagConstants.GT,
            -1, TagConstants.INTEGRALGT, -1,
	    TagConstants.FLOATINGGT, -1, -1 },
      { TagConstants.LE,
            -1, TagConstants.INTEGRALLE, -1,
	    TagConstants.FLOATINGLE, TagConstants.LOCKLE, -1 },
      { TagConstants.LT,
            -1, TagConstants.INTEGRALLT, -1,
	    TagConstants.FLOATINGLT, TagConstants.LOCKLT, -1 },
      { TagConstants.LSHIFT,
            -1, TagConstants.INTSHIFTL, TagConstants.LONGSHIFTL,
            -1, -1, -1 },
      { TagConstants.ASGLSHIFT,
            -1, TagConstants.INTSHIFTL, TagConstants.LONGSHIFTL,
            -1, -1, -1 },
      { TagConstants.RSHIFT,
            -1, TagConstants.INTSHIFTR, TagConstants.LONGSHIFTR,
            -1, -1, -1 },
      { TagConstants.ASGRSHIFT,
            -1, TagConstants.INTSHIFTR, TagConstants.LONGSHIFTR,
            -1, -1, -1 },
      { TagConstants.URSHIFT,
            -1, TagConstants.INTSHIFTRU, TagConstants.LONGSHIFTRU,
            -1, -1, -1 },
      { TagConstants.ASGURSHIFT,
            -1, TagConstants.INTSHIFTRU, TagConstants.LONGSHIFTRU,
            -1, -1, -1 },
      { TagConstants.ADD,
            -1, TagConstants.INTEGRALADD, -1,
	    TagConstants.FLOATINGADD, -1, -1 },  // see below
      { TagConstants.ASGADD,
            -1, TagConstants.INTEGRALADD, -1,
	    TagConstants.FLOATINGADD, -1, -1 },
      { TagConstants.SUB,
            -1, TagConstants.INTEGRALSUB, -1,
	    TagConstants.FLOATINGSUB, -1, -1 },
      { TagConstants.ASGSUB,
            -1, TagConstants.INTEGRALSUB, -1,
	    TagConstants.FLOATINGSUB, -1, -1 },
      { TagConstants.DIV,
            -1, TagConstants.INTEGRALDIV, -1,
	    TagConstants.FLOATINGDIV, -1, -1 },
      { TagConstants.ASGDIV,
            -1, TagConstants.INTEGRALDIV, -1,
	    TagConstants.FLOATINGDIV, -1, -1 },
      { TagConstants.MOD,
            -1, TagConstants.INTEGRALMOD, -1,
	    TagConstants.FLOATINGMOD, -1, -1 },
      { TagConstants.ASGREM,
            -1, TagConstants.INTEGRALMOD, -1,
	    TagConstants.FLOATINGMOD, -1, -1 },
      { TagConstants.STAR,
            -1, TagConstants.INTEGRALMUL, -1,
	    TagConstants.FLOATINGMUL, -1, -1 },
      { TagConstants.ASGMUL,
            -1, TagConstants.INTEGRALMUL, -1,
	    TagConstants.FLOATINGMUL, -1, -1 } };
	
    static {
      for (int i = 0; i < binary_table.length; i++) {
	  if (binary_table[i].length != 7)
	      Assert.fail("bad length, binary_table row " + i);
      }
    }

  static int getGCTagForBinary(BinaryExpr be) {

    int tag = be.getTag();
    
    Type leftType = TypeCheck.inst.getType( be.left );
    Type rightType = TypeCheck.inst.getType( be.right );

    // before consulting the table, handle "+" & "+=" on strings:
    if ((tag == TagConstants.ADD || tag == TagConstants.ASGADD) &&
	(Types.isReferenceOrNullType(leftType) ||
	 Types.isReferenceOrNullType(rightType))) {
      // this "+" or "+=" denotes string concatenation
      return TagConstants.STRINGCAT;
    }
    
    // find tag in table
    int i;

    for( i=0; i<binary_table.length; i++ ) {
      if (binary_table[i][0] == tag)
	break;
    }
    if( i==binary_table.length )
      Assert.fail("Bad tag "+TagConstants.toString(tag));
    
    // have index of correct line in i.
    int naryTag;
    if (Types.isBooleanType( leftType ) 
	&& Types.isBooleanType( rightType )) {
      naryTag = binary_table[i][1];
    } else if (Types.isLongType( leftType ) 
	       && Types.isIntegralType( rightType )) {
      if (binary_table[i][3] != -1) {
	naryTag = binary_table[i][3];
      } else {
	naryTag = binary_table[i][2];
      }
    } else if (Types.isIntegralType( leftType ) 
	       && Types.isIntegralType( rightType )) {
      naryTag = binary_table[i][2];
    } else if (Types.isNumericType( leftType ) 
	       && Types.isNumericType( rightType )) {
      // ## should convert integral args to floating point
      naryTag = binary_table[i][4];
    } else if (Types.isReferenceOrNullType( leftType ) 
	       && Types.isReferenceOrNullType( rightType )) {
      naryTag = binary_table[i][5];
    } else if (Types.isTypeType(leftType)
	       && Types.isTypeType(rightType)) {
      naryTag = binary_table[i][6];
    } else if (Types.isErrorType(leftType)) {
	ErrorSet.notImplemented(!Main.options().noNotCheckedWarnings,be.left.getStartLoc(),
				"Failed to translate some unimplemented construct");
      naryTag = -1; // dummy assignment
    } else if (Types.isErrorType(rightType)) {
	ErrorSet.notImplemented(!Main.options().noNotCheckedWarnings,be.right.getStartLoc(),
				"Failed to translate some unimplemented construct");
      naryTag = -1; // dummy assignment
    } else {
	System.out.println("LTYPE " + leftType);
	System.out.println("RTYPE " + rightType);
      Assert.fail("Bad types on tag "+TagConstants.toString(tag) );
      naryTag = -1; // dummy assignment
    }
    
    // have naryTag
    if( naryTag == -1 ) {
      Assert.fail("Bad tag/types combination at "+TagConstants.toString(tag)
		  +" left type "+leftType
		  +" right type "+rightType);
    }
    
    return naryTag;
}

  /* getGCTagForUnary uses a 2-dim lookup table.  Each entry is:

   * <pre>
   * { Unary tag,
   *   nary-tag-for-bool-args,
   *   nary-tag-for-integral,
   *   nary-tag-for-floats
   * }.
   * Use -1 if invalid combination.
   * </pre>
   */
  
  private static final int unary_table[][] 
  = { { TagConstants.UNARYSUB, -1, TagConstants.INTEGRALNEG,
	TagConstants.FLOATINGNEG },
      { TagConstants.NOT, TagConstants.BOOLNOT, -1, -1 },
      { TagConstants.BITNOT, -1, TagConstants.INTEGRALNOT, -1 },
      { TagConstants.INC, -1, TagConstants.INTEGRALADD,
	TagConstants.FLOATINGADD },
      { TagConstants.POSTFIXINC, -1, TagConstants.INTEGRALADD,
	TagConstants.FLOATINGADD },
      { TagConstants.DEC, -1, TagConstants.INTEGRALSUB,
	TagConstants.FLOATINGSUB },
      { TagConstants.POSTFIXDEC, -1, TagConstants.INTEGRALSUB,
	TagConstants.FLOATINGSUB } };

    static {
      for (int i = 0; i < unary_table.length; i++) {
	  if (unary_table[i].length != 4)
	      Assert.fail("bad length, unary table row " + i);
      }
    }

  /** TBW.  Requires e.getTag() in { UNARYSUB, NOT, BITNOT, INC,
       POSTFIXINC, DEC, POSTFIXDEC } */

  static int getGCTagForUnary(UnaryExpr e) {
    // find correct row in table
    int tag = e.getTag();
    int row;
    for (row = 0; row < unary_table.length; row++) {
      if (unary_table[row][0] == tag)
	break;
    }
    Assert.notFalse(row < unary_table.length, "Bad tag");

    // find correct column in table
    int col = 0 /*@ uninitialized */;
    Type argType = TypeCheck.inst.getType(e.expr);
    if (Types.isBooleanType(argType)) col = 1;
    else if (Types.isIntegralType(argType)) col = 2;
    else if (Types.isNumericType(argType)) col = 3;
    else if (Types.isErrorType(argType)) {
	ErrorSet.notImplemented(true || !Main.options().noNotCheckedWarnings,e.expr.getStartLoc(),
				"Failed to translate some unimplemented construct");
    } else Assert.fail("Bad type");

    int result = unary_table[row][col];
    Assert.notFalse(result != -1, "Bad type combination");
    return result;
  }
  
  public static VariableAccess makeVarAccess(GenericVarDecl decl, int loc) {
    return VariableAccess.make(decl.id, loc, decl);
  }

  /** Returns the number of variable substitutions that calls to
    * <code>trSpecExpr</code> have caused.  To find out how many times a
    * substitution was made, a caller can surround the call to
    * <code>trSpecExpr</code> by two calls to this method and compute the
    * difference.
    **/
  
  static public int getReplacementCount() {
    return cSubstReplacements;
  }
  
  private static int cSubstReplacements = 0;

  private static VariableAccess apply(Hashtable map, VariableAccess va) {
    if (map == null) {
      return va;
    }
    VariableAccess v = (VariableAccess)map.get(va.decl);
    if (v != null) {
      if (va.decl == GC.thisvar.decl) cSubstReplacements++;
      return v;
    } else {
      return va;
    }
  }
  
  public static TypeExpr trType(Type type) {
    // Other than unique-ification of type names, what distinguishes
    // Java types from the way they are represented in the verification
    // condition is that a Java array type "T[]" is represented as
    // "(array T)".  The definition of "TrType" in ESCJ 16 spells out
    // the details of this conversion.  However, unlike what ESCJ 16
    // says, the ESC/Java implementation represents types in
    // guarded-command expressions as "TypeExpr" nodes.  The conversion
    // between "[]" and "array" is done when the "TypeExpr" is converted
    // to a verification condition string.
    return TypeExpr.make(type.getStartLoc(), type.getEndLoc(), type);
  }
  
  public static void getCalledSpecs( 
			RoutineDecl decl,
			ObjectDesignator od, ExprVec ev, 
			VariableAccess resultVar,
			Hashtable sp, Hashtable st) {
//System.out.println("GCS " + decl.parent.id + " " + (decl instanceof MethodDecl ? (((MethodDecl)decl).id.toString()) : "" ) + " " + Location.toString(decl.getStartLoc()) + " " + (declStack.contains(decl)) );
    ModifierPragmaVec md = decl.pmodifiers;
    if (md == null) return;
    for (int i=0; i<md.size(); ++i) {
	ModifierPragma m = md.elementAt(i);
	switch (m.getTag()) {
	    case TagConstants.ENSURES:
	    case TagConstants.POSTCONDITION:
	     {
		Expr e = ((ExprModifierPragma)m).expr;
//System.out.println("ENSURES " + e);
		Hashtable h = new Hashtable();
		h.put(Substitute.resexpr,resultVar);
		if (od instanceof ExprObjectDesignator) {
		    if (!(((ExprObjectDesignator)od).expr instanceof ThisExpr)) {
			h.put(Substitute.thisexpr, ((ExprObjectDesignator)od).expr);
		    }
		} else if (od instanceof SuperObjectDesignator) {
			// FIXME
		    System.out.println("NOT SUPPORTED " + od.getClass());
		} // fall-through for TypeObjectDesignator or null
		    
		FormalParaDeclVec args = decl.args;
		for (int j=0; j<args.size(); ++j) {
		    h.put(args.elementAt(j), ev.elementAt(j));
		}
		e = Substitute.doSimpleSubst(h,e);
		e = trSpecExpr(e,sp,st);
		trSpecExprAuxConditions.addElement(e);
	     }

	    default:
		break;
	}
    }

	// FIXME - What about constraint clauses

	TypeDeclElemVec tdev = decl.parent.elems;
	for (int j=0; j<tdev.size(); ++j) {
	    TypeDeclElem e = tdev.elementAt(j);
	    if (!(e instanceof TypeDeclElemPragma)) continue;
	    TypeDeclElemPragma p = (TypeDeclElemPragma)e;
	    if (p.getTag() == TagConstants.INVARIANT) {
		Expr ee = ((ExprDeclPragma)p).expr;
		Hashtable h = new Hashtable();
		h.put(Substitute.resexpr,resultVar);
		if (od instanceof ExprObjectDesignator) {
		    if (!(((ExprObjectDesignator)od).expr instanceof ThisExpr)) {
			h.put(Substitute.thisexpr, ((ExprObjectDesignator)od).expr);
		    }
		} else if (od instanceof SuperObjectDesignator) {
			// FIXME
		    System.out.println("NOT SUPPORTED " + od.getClass());
		} else if (od == null) { // Constructor case
		    h.put(Substitute.thisexpr, resultVar);
		} // fall-through for TypeObjectDesignator 
		ee = Substitute.doSimpleSubst(h,ee);
		ee = trSpecExpr(ee,sp,st);
		trSpecExprAuxConditions.addElement(ee);
	    }
	}
  }
}
