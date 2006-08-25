/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava;

import escjava.backpred.FindContributors;
import escjava.prover.*;
import escjava.translate.VcToString;
import javafe.ast.ASTNode;
import javafe.ast.Expr;
import javafe.util.FatalError;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.Properties;

public class ProverManager {
  
  public static interface Listener {
    void stateChanged(int s);
  }
  public static Listener listener = null;
  
  final static private int NOTSTARTED = 0;
  final static private int STARTED = 1;
  final static private int PUSHED = 2;
  
  /*@ spec_public */ static private int status = 0;
  /*@ spec_public */ static private boolean isStarted = false;
  //@ private invariant status != NOTSTARTED <==> isStarted;
  
  static private FindContributors savedScope = null;
  
  public static boolean useSimplify = false;
  public static boolean useSammy = false;
  public static boolean useHarvey = false;
  public static boolean useCvc3 = false;

  //@ ensures isStarted && prover != null;
  synchronized
  static public void start() {
    
    if (isStarted) return;
    
    if( useSammy && (sammy == null || !sammy.started) ){
      long startTimeSammy = java.lang.System.currentTimeMillis();
      
      System.out.println("Launching demo of sammy...");
      
      Sammy.main(new String[0]);
      
      System.out.println("exiting...");
      System.exit(0);
      
    }
    
    if( useSimplify && (simplify == null)) { 
      
      long startTime = java.lang.System.currentTimeMillis();
      simplify = new Simplify();
      
      if (!Main.options().quiet)
        System.out.println("  Prover started:" + Main.timeUsed(startTime));
      
      escjava.backpred.BackPred.genUnivBackPred(simplify.subProcessToStream());
      simplify.sendCommands("");
      
    }

    if (useCvc3 && (cvc3 == null || !cvc3.started)) {
      long startTime = java.lang.System.currentTimeMillis();
      if (cvc3 == null)
        cvc3 = new Cvc3(true);

      if (!Main.options().quiet) 
        System.out.println("  Prover started:" + Main.timeUsed(startTime));

      // set any flags here (-tcc and timeout, for example)
      Properties flags = new Properties();
      flags.setProperty(" ","-timeout 0");
      cvc3.set_prover_resource_flags(flags);

      cvc3.start_prover();
      // note: the backpred is included as part of the vcGen code
    } 
    
    if (listener != null) listener.stateChanged(1);
    isStarted = true;
    status = STARTED;
    
  }
  
  synchronized
  static public Simplify prover() {
    start();
    return simplify;
  }
  
  //@ ensures status == NOTSTARTED && prover == null;
  synchronized
  static public void kill() {
    
    if(useSimplify) {
      if (simplify != null) 
        simplify.close();
      
      simplify = null;
    }
    
    if(useSammy) {
      sammy.stop_prover();
      sammy = null;
    }

    if(useCvc3) {
      cvc3.stop_prover();
      cvc3 = null;
    }
    
    if (listener != null) 
      listener.stateChanged(0);
    
    isStarted = false;
    status = NOTSTARTED;
  }
  
  synchronized
  static public void died() {
    
    if(useSimplify) {
      if (simplify != null) 
        simplify.close();
      
      simplify = null;
    }
    
    if(useSammy) {
      sammy.stop_prover();
      sammy = null;
    }
    
    if (listener != null) 
      listener.stateChanged(0);

    if(useCvc3) {
      cvc3.stop_prover();
      cvc3 = null;
    }
    
    isStarted = false;
    status = NOTSTARTED;
  }
  
  /*
   * Specific to simplify
   */
  synchronized
  static public void push(/*@ non_null @*/ Expr vc) {
    PrintStream ps = simplify.subProcessToStream();
    ps.print("\n(BG_PUSH ");
    VcToString.computePC(vc, ps);
    ps.println(")");
    simplify.sendCommands("");
  }
  
  synchronized
  static public void push(FindContributors scope) {
    start();
    if (simplify != null) {
      PrintStream ps = simplify.subProcessToStream();
      ps.print("\n(BG_PUSH ");
      escjava.backpred.BackPred.genTypeBackPred(scope, ps);
      ps.println(")");
      simplify.sendCommands("");
      savedScope = scope;
      status = PUSHED;
    }
  }
  
  //@ requires vc != null;
  // scope can be null
  //? ensures \result != null;
  synchronized
  static public Enumeration prove(Expr vc, FindContributors scope) {
   
    if (useSimplify) { 
      if (scope == null) {
        if (savedScope != null && status != PUSHED) push(savedScope);
      } else {
        if (status == PUSHED) {
          if (savedScope != scope) {
            pop();
            push(scope);
          }
        } else {
          push(scope);
        }
      }
      if (listener != null) listener.stateChanged(2);
      try {
        simplify.startProve();
        VcToString.compute(vc, simplify.subProcessToStream());
 
        Enumeration en = simplify.streamProve();
        if (listener != null) listener.stateChanged(1);
        return en;
      } catch (FatalError e) {
        died();
        return null;
      }
    }
    else {
      return null;
    }
  }
  
  /*
   * Specific to simplify
   */
  synchronized
  static public void pop() {
    if (simplify != null)
      simplify.sendCommand("(BG_POP)");
    savedScope = null;
    status = STARTED;
  }
  
  /**
   * Our Simplify instance.
   */
  //-@ monitored
  public static Simplify simplify;
  //@ private invariant isStarted ==> prover != null;
  
  /*
   * Our Sammy instance \\o \o/ o//
   */
  public static Sammy sammy;
  //@ public static model Object prover;
  //@ static represents prover <- sammy;

  /*
   * Our Cvc3 instance.
   */
  public static Cvc3 cvc3;
}
