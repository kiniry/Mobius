/* @(#)$Id$
 *
 * Copyright (C) 2006, Dependable Software Research Group, Concordia University
 */

package escjava.translate;

import java.util.Hashtable;
import java.util.Map;

import javafe.util.StackVector;
import javafe.util.Location;

import javafe.ast.*;
import javafe.util.Assert;
import javafe.util.ErrorSet;

import escjava.Main;
import escjava.Options;
import escjava.ast.ExprCmd;
import escjava.ast.GCExpr;
import escjava.ast.GuardedCmd;
import escjava.ast.GuardedCmdVec;
import escjava.ast.ExprCmd;
import escjava.ast.VarInCmd;
import escjava.ast.DynInstCmd;
import escjava.ast.SeqCmd;
import escjava.ast.Call;
import escjava.ast.CmdCmdCmd;
import escjava.ast.LoopCmd;
import escjava.ast.LabelExpr;
import escjava.ast.NaryExpr;
import escjava.ast.TagConstants;
import escjava.ast.EscPrettyPrint;

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
  private static final Options options = Main.options();
  public static boolean debug = options!=null && options.debug;

  /**
   * Creates a new <code>DefGCmd</code> instance.
   *
   */
  public DefGCmd()
  {
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
   * @return an <code>Expr</code> value.  This expression is always a Expr.
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
		fa.od.getTag() == TagConstants.EXPROBJECTDESIGNATOR) {
	      ExprObjectDesignator eod = (ExprObjectDesignator)fa.od;
	      Expr odExpr = trAndGen(eod.expr);
	      Expr refNEExpr=GC.nary(TagConstants.REFNE,odExpr,GC.nulllit);
	      GuardedCmd gc = GC.check(eod.locDot,
				       TagConstants.CHKNULLPOINTER,
				       refNEExpr,
				       Location.NULL);
	      this.code.addElement(gc);
	    }
	    return TrAnExpr.trSpecExpr(e, minHMap4Tr(), null);
	}
      
	case TagConstants.ARRAYREFEXPR: {
	  ArrayRefExpr are=(ArrayRefExpr)e;
	  Expr array=this.trAndGen(are.array);
	  Expr index=this.trAndGen(are.index);
	  // Null check
	  Expr refNEExpr=GC.nary(TagConstants.REFNE,
				 array,GC.nulllit);
	  GuardedCmd gc = GC.check(are.locOpenBracket,
				   TagConstants.CHKNULLPOINTER,
				   refNEExpr,Location.NULL);
	  this.code.addElement(gc);
	  // Negative index check
	  Expr indexNeg=GC.nary(TagConstants.INTEGRALLE,
				GC.zerolit, index);
	  GuardedCmd gc1=GC.check(are.locOpenBracket,
				  TagConstants.CHKINDEXNEGATIVE,
				  indexNeg,Location.NULL);
	  this.code.addElement(gc1);
	  // Index too big check
	  Expr length= GC.nary(TagConstants.ARRAYLENGTH, array);
	  Expr index2Big=GC.nary(TagConstants.INTEGRALLT, 
				 index, length);
	  GuardedCmd gc2=GC.check(are.locOpenBracket,
				  TagConstants.CHKINDEXTOOBIG,
				  index2Big,Location.NULL);
	  this.code.addElement(gc2);
	  return TrAnExpr.trSpecExpr(e, minHMap4Tr(), null);
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
	  {
	    BinaryExpr be = (BinaryExpr)e;
	    Expr leftExpr = this.trAndGen(be.left);
	    Expr notLeftExpr=GC.nary(TagConstants.BOOLNOT,leftExpr);
	    this.code.push();
	    Expr rightExpr = this.trAndGen(be.right);
	    GuardedCmd rightGC=this.popFromCode();
	    GuardedCmd leftGC=GC.assume(GC.truelit);
	    GuardedCmd notleftGC=GC.assume(rightExpr);
	    this.code.
	      addElement(GC.ifcmd(notLeftExpr,
				  GC.assume(GC.truelit),
				  rightGC));
	    int newtag = TrAnExpr.getGCTagForBinary(be);
	    return GC.nary(e.getStartLoc(),e.getEndLoc(),
			   newtag,leftExpr,rightExpr);
	  }
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
	    return TrAnExpr.trSpecExpr(e, minHMap4Tr(), null);
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
		me.od instanceof ExprObjectDesignator) {
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
	    return TrAnExpr.trSpecExpr(e, minHMap4Tr(), null);
	}
      
	case TagConstants.NEWARRAYEXPR: {
	    if(true) { break; } else { notImpl(e); }
	    return null;
	}
      
	case TagConstants.EXPLIES: 
	  {
	    BinaryExpr be = (BinaryExpr)e;
	    Expr leftExpr = this.trAndGen(be.right);
	    Expr notLeftExpr=GC.nary(TagConstants.BOOLNOT,leftExpr);
	    this.code.push();
	    Expr rightExpr = this.trAndGen(be.left);
	    GuardedCmd rightGC=this.popFromCode();
	    GuardedCmd leftGC=GC.assume(GC.truelit);
	    GuardedCmd notleftGC=GC.assume(rightExpr);
	    this.code.
	      addElement(GC.ifcmd(notLeftExpr,
				  GC.assume(GC.truelit),
				  rightGC));
	    int newtag = TagConstants.BOOLIMPLIES;
	    return GC.nary(e.getStartLoc(),e.getEndLoc(),
			   newtag,leftExpr,rightExpr);
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
	// In all cases that fall through, add the ASSERT true; command.
	GuardedCmd gc=ExprCmd.make(TagConstants.ASSERTCMD, GC.truelit, e.getStartLoc());
	this.code.addElement(gc);
	// In all cases that fall through, simply translate e into a GC expr.
	return TrAnExpr.trSpecExpr(e, minHMap4Tr(), null);
    }

    private void notImpl(Expr e) {
	ErrorSet.notImplemented(!Main.options().noNotCheckedWarnings,
				e.getStartLoc(), e.toString());
    }

    Hashtable minHMap4Tr() {
	// The returned map is only needed for constructors, but since
	// general type checking will have been done, we can simply
	// use the same map in all cases (constructor or not).
	Hashtable map = new Hashtable();
	map.put(GC.thisvar.decl, GC.resultvar);
	return(null); // Return null because its preferrable to see 
	              // <code>this</code> in IDC GCs and not <code>RES</code>
	              // which is used in constructors.  FIXME so that
		          // the distinction between methods and constructors is
		          // made.
    }

  
  /**
   * Describe <code>morfAsserts</code> method here.
   *
   * @param gc a <code>GuardedCmd</code> value
   * @param ante an <code>Expr</code> value
   * @return a <code>GuardedCmd</code> value
   */
  public GuardedCmd morfAsserts(/*@ non_null */ GuardedCmd gc,
				/*@ non_null */ Expr ante)
  {
//     if (debug)
//     {
//       System.out.println(this.traceMethod() + 
// 			 TagConstants.toString(gc.getTag()));
//     }

    switch (gc.getTag()) {

    case TagConstants.ASSERTCMD: {
      ExprCmd ec=(ExprCmd)gc;
      Assert.notFalse(ec.pred.getTag() == TagConstants.LABELEXPR ||
		      LiteralExpr.isValidTag(ec.pred.getTag()));
      switch (ec.pred.getTag()) {
      case TagConstants.LABELEXPR:
	{
	  LabelExpr le=(LabelExpr)ec.pred;
	  le.expr=GC.implies(ante,le.expr);
	  break;
	}
	
      case TagConstants.BOOLEANLIT: 
	{
	  LiteralExpr le=(LiteralExpr)ec.pred;
	  Expr newE = GC.implies(ante,le);
	  ec.pred=newE;
	  break;
	}
      default:
	//@ unreachable;
	Assert.notFalse(false);
	break;
      }
      return(ec);
    }


    case TagConstants.SKIPCMD:
    case TagConstants.RAISECMD:
    case TagConstants.ASSUMECMD:
    case TagConstants.GETSCMD:
    case TagConstants.SUBGETSCMD:
    case TagConstants.SUBSUBGETSCMD:
    case TagConstants.RESTOREFROMCMD:
      return(gc);

    case TagConstants.VARINCMD: {
      VarInCmd vc=(VarInCmd)gc;
      vc.g=this.morfAsserts(vc.g,ante);
      return(vc);
    }

    case TagConstants.DYNINSTCMD: {
      DynInstCmd dc=(DynInstCmd)gc;
      dc.g=this.morfAsserts(dc.g,ante);
      return(dc);
    }

    case TagConstants.SEQCMD: {
      SeqCmd sc=(SeqCmd)gc;
      for (int i=0;i<sc.cmds.size();i++) {
	GuardedCmd gc1=sc.cmds.elementAt(i);
	gc=this.morfAsserts(gc1,ante);
	sc.cmds.setElementAt(gc1,i);
      }
      return(sc);
    }

    case TagConstants.CALL: {
      Call call=(Call)gc;
      call.desugared=this.morfAsserts(call.desugared,ante);
      return(call);
    }

    case TagConstants.TRYCMD:
    case TagConstants.CHOOSECMD: {
      CmdCmdCmd tc = (CmdCmdCmd)gc;
      tc.g1=this.morfAsserts(tc.g1,ante);
      tc.g2=this.morfAsserts(tc.g2,ante);
      return(tc);
    }

    case TagConstants.LOOPCMD: {
      LoopCmd lp = (LoopCmd)gc;
      lp.guard=this.morfAsserts(lp.guard,ante);
      lp.body=this.morfAsserts(lp.body,ante);
      return(lp);
    }

    default:
      //@ unreachable;
      Assert.notFalse(false);
      return null;
    }
  }


  /**
   * Expects a postcondition in the following form:
   * A && P1 && ... && Pn ==> Q. 
   * It then extracts the antecedent, translates it into a <code>GCExpr</code>
   * and returns it.
   *
   * @param post an <code>Expr</code> value
   * @return an <code>Expr</code> value
   */
  public static Expr reapAntecedent(Expr post)
  {
    // Fail if this is not an implication.
    //Assert.notFalse(post.getTag() == TagConstants.IMPLIES);
    if (post.getTag() != TagConstants.IMPLIES) {
      return(GC.truelit);
    }
    
    // Get the antecedent.
    Expr e=((BinaryExpr)post).left;

    return(e);
  }

  /**
   * Expects a postcondition in the following form:
   * A && P1 && ... && Pn ==> Q. 
   * It then extracts the consequent, and returns it.
   *
   * @param post an <code>Expr</code> value
   * @return an <code>Expr</code> value
   */
  public static Expr reapConsequent(Expr post) 
  {
    // Fail if this is not an implication.
    //Assert.notFalse(post.getTag() == TagConstants.IMPLIES,post.toString());
    if (post.getTag() != TagConstants.IMPLIES) {
      if (debug) {
	System.out.println("GK-Trace: WARNING: postcondition not an implication"+
			   "\n\t\t"+post.toString());
      }
      return(post);
    }
    // Get the concequent.
    Expr e=((BinaryExpr)post).right;
    return(e);
  }

  /**
   * Iterates through a tree of ASTNodes denoting number of conjunctions.
   * It reaps the leftmost one and rebuilds the remaining ones.
   *
   * @param e an <code>Expr</code> value
   * @return an <code>Expr</code> value
   */
  public static Expr reapLeftmostConjunct(Expr e)
  {
    Assert.notFalse(e.getTag() == TagConstants.AND,e.toString());
    BinaryExpr be = (BinaryExpr)e;
    Expr newExpr;
    if (be.left.getTag()==TagConstants.AND) {
      Expr e1=reapLeftmostConjunct(be.left);
      newExpr=BinaryExpr.make(TagConstants.AND,e1,be.right,be.locOp);
    } else {
      newExpr=be.right;
    }
    return(newExpr);
  }


  /**
   * This method will obtain a postcondition in the form of an implication, where
   * the antecedent is the conjointed req. cl. exprs. along with some other
   * predicates ESC adds.  It will break it into its antecedent and consequent
   * expressions.  It will then call addConj2Map() and use the antecedent and 
   * the condition label to build a unique key so that the pair of antecedent, 
   * consequent is stored in the map.
   *
   * @param label an <code>int</code> value
   * @param mapAnte2AntePost a <code>Map</code> value
   * @param pred an <code>Expr</code> value
   */
  public static void processPostcondition(int  label,
					  Map  mapAnte2AntePost,
					  Expr pred)
  {
    // Get the antecedent
    Expr ante=DefGCmd.reapAntecedent(pred);
    // Get the consequent.
    Expr post=DefGCmd.reapConsequent(pred);
    if (debug) {
      System.err.println("\tCOND: "+TagConstants.toString(label));
      System.err.println("\tANTE: "+EscPrettyPrint.inst.toString(ante));
      System.err.println("\tPOST: "+EscPrettyPrint.inst.toString(post));
    }

    // Conjoin the postconditions per antecedents found.
    addConj2Map(label,mapAnte2AntePost, ante, post);
  }

  /**
   * Uses the ante and label values to build a key where by it will store
   * the ante expression along with the conjointed post values that have the
   * same ante and the same label.
   *
   * @param mapAnte2AntePost a <code>Map</code> value
   * @param ante an <code>Expr</code> value
   * @param post an <code>Expr</code> value
   */
  public static void addConj2Map(int label,
				 Map mapAnte2AntePost,
				 Expr ante, 
				 Expr post)
  {
    Object [] antePost=null;
    String k=label+ante.toString();
    if (!mapAnte2AntePost.containsKey(k)) {
      if (debug) {
	System.out.println("\tCONJ: "+EscPrettyPrint.inst.toString(post));
      }
      antePost=new Object[2];
      antePost[0]=ante;
      antePost[1]=post;
    } else {
      antePost =(Object[])mapAnte2AntePost.get(k);
      Expr e=(Expr)(antePost[1]);
      BinaryExpr be=BinaryExpr.make(TagConstants.AND, e, post, Location.NULL);
      if (debug) {
	System.out.println("\tCONJ: "+EscPrettyPrint.inst.toString(be));
      }
      antePost[1]=be;
    }
    mapAnte2AntePost.put(k,antePost);
  }

  private String traceMethod() 
  {
    Throwable t=new Throwable();
    StackTraceElement [] stes=t.getStackTrace();
    if (stes != null && stes.length != 0) {
      return("GK-Trace : " + stes[1]);
    }
    return("GK-Trace : NA");
  }
}
