/* @(#)$Id$
 *
 * Copyright (C) 2006, Dependable Software Research Group, Concordia University
 */

package escjava.translate;

import java.util.Hashtable;

import javafe.util.StackVector;
import javafe.util.Location;

import javafe.ast.Expr;
import javafe.ast.VariableAccess;
import javafe.ast.ThisExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.BinaryExpr;
import javafe.ast.CondExpr;
import javafe.ast.ParenExpr;
import javafe.ast.FieldAccess;
import javafe.ast.InstanceOfExpr;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.MethodInvocation;
import escjava.ast.Modifiers;

import escjava.Main;
import escjava.ast.GuardedCmd;
import escjava.ast.GuardedCmdVec;
import escjava.ast.ExprCmd;
import escjava.ast.TagConstants;
import escjava.ast.GCExpr;
import escjava.ast.LabelExpr;

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
  public Expr trAndGen(Expr x)
  {
    Expr result=null;
    if (debug)
    {
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

  private Hashtable minHMap4Tr()
  {
    Hashtable map = new Hashtable();
    map.put(GC.thisvar.decl, GC.resultvar);
    return(map);
  }

  private String traceMethod()
  {
    Throwable t=new Throwable();
    StackTraceElement [] stes=t.getStackTrace();
    if (stes!=null || stes.length!=0)
    {
      return("GK-Trace : " + stes[1]);
    }
    return("GK-Trace : NA");
  }


}
