/* @(#)$Id$
 *
 * Copyright (C) 2006, Dependable Software Research Group, Concordia University
 */

package escjava.translate;

import java.util.Hashtable;

import javafe.util.StackVector;
import javafe.util.Location;

import javafe.ast.*;
import javafe.util.Assert;
import javafe.util.ErrorSet;

import escjava.Main;
import escjava.ast.ExprCmd;
import escjava.ast.GCExpr;
import escjava.ast.GuardedCmd;
import escjava.ast.GuardedCmdVec;
import escjava.ast.LabelExpr;
import escjava.ast.NaryExpr;
import escjava.ast.TagConstants;

/**
 * Class <code>DefGCmd</code> implements the definedness guarded commands
 * for the requires clauses.  The functionality is invoced by adding the -idc 
 * option to escj.
 * Supported functionality:
 *  - <code>div</code> and <code>mod</code> operators generate CHKARITHMETIC checks
 *  - Conditional<code>&&</code> and <code>or</code> operators generate ifcmd
 *    guarded commands.
 *  - Dereferrencing is partially supported.  Still working on this.
 * Usage:
 *  - DefGCmd defGCmd=new DefGCmd();
 *  - defGCmd.trAndGen(expr); // expr is an untranslated expression.
 *  - GuardedCmd gc=defGCmd.popFromCode();
 * NOTE: This is work inprogress and its fairly experimental, 
 * so bear with us for the time being :). Use at your own risk.
 *
 * @author <a href="mailto:g_karab@cs.concordia.ca">George Karabotsos</a>
 * @version 1.0
 */
public class DefGCmd
{
  /**
   * <code>code</code> is the StackVector instance and is used to hold the
   * definednes guarded commands for each method.
   *
   */
  private StackVector code;
  
  /**
   * <code>debug</code> is a central and convinient way of turning on/off
   * debug messages.
   *
   */
  public static boolean debug = Main.options().debug;

  /**
   * Creates a new <code>DefGCmd</code> instance.
   *
   */
  public DefGCmd()
  {
    // debug = Main.options().debug;
    if (debug) System.err.println(this.traceMethod());
    this.code=new StackVector();
    this.code.push();
  }

  /**
   * Convenient shorthand for the command in the return statement.
   *
   * @return a <code>GuardedCmd</code> value
   */
  public GuardedCmd popFromCode()
  {
    return(GC.seq(GuardedCmdVec.popFromStackVector(code)));
  }

  /**
   * This is the workhorse method.  In this method we go through the 
   * <code>Expr</code> tree and generate the appropriate guarded commands.
   * The guarded commands are generated and stored in the <code>code</code>
   * field.
   *
   * @param x an <code>Expr</code> value
   * @return an <code>Expr</code> value.  This expression is always a GCExpr.
   * its not set as GCExpr so that we do not get type mismatch between client
   * methods.
   */

    /** (new trAndGent)
     */

    public Expr trAndGen(Expr e) {
	int tag = e.getTag();
	switch (tag) {
	case TagConstants.THISEXPR: {
	    break;
        }
      
	    // Literals (which are already GCExpr's)
	case TagConstants.BOOLEANLIT: 
	case TagConstants.CHARLIT:
	case TagConstants.DOUBLELIT: 
	case TagConstants.FLOATLIT:
	case TagConstants.INTLIT:
	case TagConstants.LONGLIT:
	case TagConstants.NULLLIT: {
	    break;
	}

	case TagConstants.STRINGLIT: {
	    break;
	}
      
	case TagConstants.RESEXPR: {
	    break;
	}
      
	case TagConstants.LOCKSETEXPR: {
	    break;
	}      

	case TagConstants.VARIABLEACCESS: {
	    break;
	}
      
	case TagConstants.FIELDACCESS: {
	    // <expr>.id
	    FieldAccess fa = (FieldAccess)e;
	    if (!Modifiers.isStatic(fa.decl.modifiers) &&
		fa.od.getTag() == TagConstants.EXPROBJECTDESIGNATOR) 
		{
		    ExprObjectDesignator eod = (ExprObjectDesignator)fa.od;
		    Expr odExpr = trAndGen(eod.expr);
		    Expr refNEExpr=GC.nary(TagConstants.REFNE,odExpr,GC.nulllit);
		    GuardedCmd gc = GC.check(eod.locDot,
					     TagConstants.CHKNULLPOINTER,
					     refNEExpr,
					     Location.NULL);
		    this.code.addElement(gc);
		}
	    break;
	}
      
	case TagConstants.ARRAYREFEXPR: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.ARRAYRANGEREFEXPR:
	case TagConstants.WILDREFEXPR: {
	    break;
	}
      
	case TagConstants.PARENEXPR: {
	    ParenExpr pe = (ParenExpr)e;
	    // TrAnExpr.trSpecExpr drops the parenthesis, so do I :).
	    return trAndGen(pe.expr);
	}
      
	    // Unary operator expressions
      
	case TagConstants.UNARYSUB: 
	case TagConstants.NOT: 
	case TagConstants.BITNOT: {
	    UnaryExpr ue = (UnaryExpr)e;
	    int newtag = TrAnExpr.getGCTagForUnary(ue);
	    return GC.nary(ue.getStartLoc(), ue.getEndLoc(), newtag, 
			   trAndGen(ue.expr));
	}
      
	case TagConstants.UNARYADD: {
	    UnaryExpr ue = (UnaryExpr)e;
	    return trAndGen(ue.expr);
	}
      
	case TagConstants.TYPEOF:
	case TagConstants.ELEMTYPE:
	case TagConstants.MAX: {
	    NaryExpr ne = (NaryExpr)e;
	    int n = ne.exprs.size();
	    ExprVec exprs = ExprVec.make(n);
	    for (int i = 0; i < n; i++) {
		exprs.addElement(trAndGen(ne.exprs.elementAt(i)));
	    }
	    return GC.nary(ne.getStartLoc(), ne.getEndLoc(), ne.getTag(), exprs);
	}

	case TagConstants.DTTFSA: {
	    // take this expr as atomic -- could to more (see
	    // TrAnExpr.trSpecExpr), but probably isn't worth it
	    break;
	}
      
	case TagConstants.ELEMSNONNULL: {
	    NaryExpr ne = (NaryExpr)e;
	    VariableAccess elems = TrAnExpr.makeVarAccess(GC.elemsvar.decl,
							  e.getStartLoc());
	    return GC.nary(ne.getStartLoc(), ne.getEndLoc(), ne.getTag(),
			   trAndGen(ne.exprs.elementAt(0)), elems);
	}
      
	    // Binary operator expressions
      
	case TagConstants.OR: {
	    BinaryExpr be = (BinaryExpr)e;
	    Expr leftExpr = this.trAndGen(be.left);
	    this.code.push();
	    Expr rightExpr = this.trAndGen(be.right);
	    GuardedCmd rightGC=this.popFromCode();
	    GuardedCmd leftGC=GC.assume(GC.truelit);
	    GuardedCmd notleftGC=GC.assume(rightExpr);
	    this.code.
		addElement(GC.ifcmd(leftExpr,
				    GC.assume(GC.truelit),
				    rightGC));
	    return GC.nary(e.getStartLoc(),e.getEndLoc(),
			   TagConstants.BOOLOR,
			   leftExpr,rightExpr);
	}

	case TagConstants.AND: {
	    BinaryExpr be = (BinaryExpr)e;
	    Expr leftExpr  = this.trAndGen(be.left);
	    this.code.push();
	    Expr rightExpr = this.trAndGen(be.right);
	    GuardedCmd rightGC=this.popFromCode();
	    GuardedCmd leftGC=GC.assume(leftExpr);
	    GuardedCmd notLeftGC=GC.assume(GC.truelit);
	    this.code.
		addElement(GC.ifcmd(leftExpr,rightGC,notLeftGC));
	    return GC.nary(e.getStartLoc(),e.getEndLoc(),
			   TagConstants.BOOLAND,
			   leftExpr,rightExpr);
	}

	case TagConstants.IMPLIES:
	case TagConstants.IFF:
	case TagConstants.NIFF:
	case TagConstants.BITOR:
	case TagConstants.BITAND:
	case TagConstants.BITXOR:
	    // fall through to the next group ...
    
	case TagConstants.EQ:
	case TagConstants.NE:
	case TagConstants.LSHIFT:
	case TagConstants.RSHIFT:
	case TagConstants.URSHIFT:
	    // fall through to the next group ...
      
	case TagConstants.GE:
	case TagConstants.GT:
	case TagConstants.LE:
	case TagConstants.LT:
	case TagConstants.ADD:
	case TagConstants.SUB:
	case TagConstants.STAR: {
	    BinaryExpr be = (BinaryExpr)e;
	    Expr leftExpr  = this.trAndGen(be.left);
	    Expr rightExpr = this.trAndGen(be.right);
	    int newtag= TrAnExpr.getGCTagForBinary(be);
	    return GC.nary(e.getStartLoc(), e.getEndLoc(),
			   newtag, leftExpr, rightExpr);
	}

	case TagConstants.DIV:
	case TagConstants.MOD: {
	    BinaryExpr be = (BinaryExpr)e;
	    Expr leftExpr  = trAndGen(be.left);
	    Expr rightExpr = trAndGen(be.right);
	    Expr neZeroExpr=GC.nary(TagConstants.INTEGRALNE,
				    rightExpr,
				    GC.zerolit);
	    GuardedCmd gc=GC.check(be.locOp,
				   TagConstants.CHKARITHMETIC,
				   neZeroExpr,
				   Location.NULL);
	    this.code.addElement(gc);
	    int newtag= TrAnExpr.getGCTagForBinary(be);
	    return GC.nary(e.getStartLoc(), e.getEndLoc(),
			   newtag, leftExpr, rightExpr);
	}
      
	case TagConstants.NEWINSTANCEEXPR: {
	    NewInstanceExpr me = (NewInstanceExpr)e;
	    // ensure that definedness cond are generated
	    // for arguments to constructor ...
	    for (int i=0; i<me.args.size(); ++i) {
		trAndGen(me.args.elementAt(i));
	    }
	    // but then let TrAnExpr actually do the translation ...
	    break;
	}
      
	case TagConstants.METHODINVOCATION: {
	    MethodInvocation me = (MethodInvocation)e;

	    // ensure that definedness cond are generated
	    // for arguments to method ...

	    // (eventually we will want to save the result so that we can use
	    // the translated actual param in a call to test the precondition of 
	    // the method)

	    for (int i=0; i<me.args.size(); ++i) {
		trAndGen(me.args.elementAt(i));
	    }

	    if (!Modifiers.isStatic(me.decl.modifiers) &&
		me.od instanceof ExprObjectDesignator) 
		{
		    // Expr ex = ((ExprObjectDesignator)me.od).expr;
		    ExprObjectDesignator eod = (ExprObjectDesignator)me.od;
		    Expr odExpr = trAndGen(eod.expr);
		    Expr refNEExpr=GC.nary(TagConstants.REFNE,odExpr,GC.nulllit);
		    GuardedCmd gc = GC.check(eod.locDot,
					     TagConstants.CHKNULLPOINTER,
					     refNEExpr,
					     Location.NULL);
		    this.code.addElement(gc);
		}
	    break;
	}
      
	case TagConstants.NEWARRAYEXPR: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.EXPLIES: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.SUBTYPE: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	    // Other expressions
      
	case TagConstants.CONDEXPR: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.INSTANCEOFEXPR: {
	    break;
	}
      
	case TagConstants.CASTEXPR: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.CLASSLITERAL: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.TYPEEXPR: {
	    break;
	}
      
	case TagConstants.REACH: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.NUM_OF:
	case TagConstants.SUM:
	case TagConstants.PRODUCT: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.MIN:
	case TagConstants.MAXQUANT: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.FORALL:
	case TagConstants.EXISTS: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.SETCOMPEXPR: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.LABELEXPR: {
	    LabelExpr le = (LabelExpr)e;
	    return LabelExpr.make(le.getStartLoc(),
				  le.getEndLoc(),
				  le.positive,
				  le.label,
				  this.trAndGen(le.expr));
	}
      
	case TagConstants.PRE: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.FRESH: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.DOTDOT: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}      

	case TagConstants.NOWARN_OP:
	case TagConstants.WACK_NOWARN:
	case TagConstants.WARN_OP:
	case TagConstants.WARN: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.IS_INITIALIZED:
	case TagConstants.INVARIANT_FOR: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	} 
      
	case TagConstants.SPACE:
	case TagConstants.WACK_WORKING_SPACE:
	case TagConstants.WACK_DURATION: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.NOTHINGEXPR:
	case TagConstants.EVERYTHINGEXPR:
	    return null;
      
	case TagConstants.NOTMODIFIEDEXPR: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	default:
	    Assert.fail("UnknownTag<"+e.getTag()+","+
			TagConstants.toString(e.getTag())+"> on "+e+ " " +
			Location.toString(e.getStartLoc()));
	    return null; // dummy return
	}

	// In all cases that fall through, simply translate e into a GC expr.
	return TrAnExpr.trSpecExpr(e, minHMap4Tr(), null);
    }

    private void notImpl(Expr e) {
	ErrorSet.notImplemented(!Main.options().noNotCheckedWarnings,
				e.getStartLoc(), e.toString());
    }

    private Hashtable minHMap4Tr() {
	// The returned map is only needed for constructors, but since
	// general type checking will have been done, we can simply
	// use the same map in all cases (constructor or not).
	Hashtable map = new Hashtable();
	map.put(GC.thisvar.decl, GC.resultvar);
	return(map);
    }

    private String traceMethod() {
	Throwable t=new Throwable();
	StackTraceElement [] stes=t.getStackTrace();
	if (stes!=null || stes.length!=0)
	    {
		return("GK-Trace : " + stes[1]);
	    }
	return("GK-Trace : NA");
    }


  /** prev impl. of trAndGen ... to be removed soon 
   */
    public Expr trAndGenPrev(Expr x)
    {
	Expr result=null;
	if (debug) {
	    System.err.println(this.traceMethod());
	    System.err.println("\t\t"+x.getClass());
	}

	// VariableAccess
	if (x instanceof VariableAccess)
	    {
		VariableAccess va=(VariableAccess)x;
		result = va;
		this.code.addElement(ExprCmd.make(TagConstants.ASSERTCMD,
						  GC.truelit,
						  va.loc));
	    } 
    
	// LiteralExpr
	else if (x instanceof LiteralExpr)
	    {
		LiteralExpr le=(LiteralExpr)x;
		result = le;
		this.code.addElement(ExprCmd.make(TagConstants.ASSERTCMD,
						  GC.truelit,
						  le.loc));
	    } 
    
	// ThisExpr
	else if (x instanceof ThisExpr)
	    {
		ThisExpr te=(ThisExpr)x;
		this.code.addElement(ExprCmd.make(TagConstants.ASSERTCMD,
						  GC.truelit,
						  te.loc));
		Hashtable map = this.minHMap4Tr();
		result=TrAnExpr.trSpecExpr(x,map,null);
	    }

	// LabelExpr
	else if (x instanceof LabelExpr)
	    {
		LabelExpr le = (LabelExpr)x;
		// Return a LabelExpr with LabelExpr.expr=this.trAndGen(le.expr)
		result=LabelExpr.make(le.getStartLoc(),
				      le.getEndLoc(),
				      le.positive,
				      le.label,
				      this.trAndGen(le.expr));
	    }
    
	// BinaryExpr
	else if (x instanceof BinaryExpr)
	    {
		BinaryExpr be=(BinaryExpr)x;
		if (debug)
		    System.err.println("GK-Trace-TAG: "+TagConstants.toString(be.getTag()));
		switch (be.getTag())
		    {
			// DIV/MOD
		    case TagConstants.DIV:
		    case TagConstants.MOD:
			{
			    Expr leftExpr  = this.trAndGen(be.left);
			    Expr rightExpr = this.trAndGen(be.right);
			    Expr neZeroExpr=GC.nary(TagConstants.INTEGRALNE,
						    be.right,
						    GC.zerolit);
			    GuardedCmd gc=GC.check(be.locOp,
						   TagConstants.CHKARITHMETIC,
						   neZeroExpr,
						   Location.NULL);
			    this.code.addElement(gc);
			    int newtag= TrAnExpr.getGCTagForBinary(be);
			    result=GC.nary(x.getStartLoc(), x.getEndLoc(),
					   newtag, leftExpr, rightExpr);
			}
			break;
			// Conditional AND.
		    case TagConstants.AND:
			{
			    Expr leftExpr  = this.trAndGen(be.left);
			    this.code.push();
			    Expr rightExpr = this.trAndGen(be.right);
			    GuardedCmd rightGC=this.popFromCode();
			    GuardedCmd leftGC=GC.assume(leftExpr);
			    GuardedCmd notLeftGC=GC.assume(GC.truelit);
			    this.code.
				addElement(GC.ifcmd(leftExpr,rightGC,notLeftGC));
			    result=GC.nary(x.getStartLoc(),x.getEndLoc(),
					   TagConstants.BOOLAND,
					   leftExpr,rightExpr);
			}
			break;
			// Conditional OR
		    case TagConstants.OR:
			{
			    Expr leftExpr = this.trAndGen(be.left);
			    this.code.push();
			    Expr rightExpr = this.trAndGen(be.right);
			    GuardedCmd rightGC=this.popFromCode();
			    GuardedCmd leftGC=GC.assume(GC.truelit);
			    GuardedCmd notleftGC=GC.assume(rightExpr);
			    this.code.
				addElement(GC.ifcmd(leftExpr,
						    GC.assume(GC.truelit),
						    rightGC));
			    result=GC.nary(x.getStartLoc(),x.getEndLoc(),
					   TagConstants.BOOLOR,
					   leftExpr,rightExpr);
			}
			break;
			// Remaining operators.
		    default:
			{
			    Expr leftExpr  = this.trAndGen(be.left);
			    Expr rightExpr = this.trAndGen(be.right);
			    int newtag= TrAnExpr.getGCTagForBinary(be);
			    result=GC.nary(x.getStartLoc(), x.getEndLoc(),
					   newtag, leftExpr, rightExpr);
			}
			break;
		    }
	    }

	// Conditional Expr ( P ? x : y )
	else if (x instanceof CondExpr)
	    {
		CondExpr ce=(CondExpr)x;
		Expr tstExpr=this.trAndGen(ce.test);
		this.code.push();
		Expr thnExpr=this.trAndGen(ce.thn);
		GuardedCmd thnGC=this.popFromCode();
		this.code.push();
		Expr elsExpr=this.trAndGen(ce.els);
		GuardedCmd elsGC=this.popFromCode();
		this.code.addElement(GC.ifcmd(tstExpr,thnGC,elsGC));
		Hashtable map = this.minHMap4Tr();
		result=TrAnExpr.trSpecExpr(x,map,null);
	    }

	// FieldAccess
	else if (x instanceof FieldAccess)
	    {
		FieldAccess fa = (FieldAccess)x;
		// FIXME: Only object methods are handled.
		if (!Modifiers.isStatic(fa.decl.modifiers))
		    {
			switch (fa.od.getTag())
			    {
				// FIXME: Only ExprObjectDesignator objects are treated.
				//        anything else will generate an exception.
				//        Still is needed to decide what to do for the others.
			    case TagConstants.EXPROBJECTDESIGNATOR:
				{
				    ExprObjectDesignator eod = (ExprObjectDesignator)fa.od;
				    Expr odExpr=this.trAndGen(eod.expr);
				    Expr refNEExpr=GC.nary(TagConstants.REFNE,odExpr,GC.nulllit);
				    GuardedCmd gc = GC.check(eod.locDot,
							     TagConstants.CHKNULLPOINTER,
							     refNEExpr,
							     Location.NULL);
				    this.code.addElement(gc);
				    // Prepare the result
				    Hashtable map = this.minHMap4Tr();
				    result=TrAnExpr.trSpecExpr(x,map,null);
				}
				break;
			    default:
				if (true) throw new RuntimeException(fa.od.toString());
			    }
		    }
	    }

	// MethodInvocation
	else if (x instanceof MethodInvocation)
	    {
		MethodInvocation mi = (MethodInvocation)x;
		// FIXME: Only object methods are handled.
		if (!Modifiers.isStatic(mi.decl.modifiers))
		    {
			switch (mi.od.getTag())
			    {
				// FIXME: Only ExprObjectDesignator objects are treated.
				//        anything else will generate an exception.
				//        Still is needed to decide what to do for the others.
			    case TagConstants.EXPROBJECTDESIGNATOR:
				{
				    ExprObjectDesignator eod = (ExprObjectDesignator)mi.od;
				    Expr odExpr=this.trAndGen(eod.expr);
				    Expr refNEExpr=GC.nary(TagConstants.REFNE,odExpr,GC.nulllit);
				    GuardedCmd gc = GC.check(eod.locDot,
							     TagConstants.CHKNULLPOINTER,
							     refNEExpr,
							     Location.NULL);
				    this.code.addElement(gc);
				    // Prepare the result
				    Hashtable map = this.minHMap4Tr();
				    result=TrAnExpr.trSpecExpr(x,map,null);
				}
				break;
			    default:
				if (true) throw new RuntimeException(mi.od.toString());
			    }
		    }
	    }

	// InstanceOfExpr
	else if (x instanceof InstanceOfExpr)
	    {
		Hashtable map = this.minHMap4Tr();
		result=TrAnExpr.trSpecExpr(x,map,null);
	    }

	// ParenExpr
	else if (x instanceof ParenExpr)
	    {
		ParenExpr pe=(ParenExpr)x;
		// TrAnExpr.trSpecExpr drops the parenthesis, so do I :).
		result = this.trAndGen(pe.expr);
	    }
    
	// Generate an exception for all remaining cases.
	else
	    {
		if (true) throw new RuntimeException(x.toString());
	    }
	return(result==null ? GC.truelit : result);
    }
}
