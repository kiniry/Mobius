/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava;

import escjava.backpred.FindContributors;
import escjava.prover.Simplify;
import escjava.translate.VcToString;
import javafe.ast.ASTNode;
import javafe.ast.Expr;
import javafe.util.FatalError;
import java.io.PrintStream;
import java.util.Enumeration;


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

    //@ ensures isStarted && prover != null;
    synchronized
    static public void start() {
	if (isStarted) return;
	long startTime = java.lang.System.currentTimeMillis();
	prover = new Simplify();
	
	if (listener != null) listener.stateChanged(1);
	if (!Main.options().quiet)
	    System.out.println("  Prover started:" + Main.timeUsed(startTime));

	escjava.backpred.BackPred.genUnivBackPred(prover.subProcessToStream());
	prover.sendCommands("");
	isStarted = true;
	status = STARTED;
    }

    synchronized
    static public Simplify prover() {
	start();
	return prover;
    }

    //@ ensures status == NOTSTARTED && prover == null;
    synchronized
    static public void kill() {
	if (prover != null) prover.close();
	if (listener != null) listener.stateChanged(0);
	prover = null;
	isStarted = false;
	status = NOTSTARTED;
    }

    synchronized
    static public void died() {
	if (prover != null) prover.close();
	if (listener != null) listener.stateChanged(0);
	prover = null;
	isStarted = false;
	status = NOTSTARTED;
    }

    synchronized
    static public void push(Expr vc) {
	PrintStream ps = prover.subProcessToStream();
	ps.print("\n(BG_PUSH ");
	VcToString.computePC(vc, ps);
	ps.println(")");
	prover.sendCommands("");
    }

    synchronized
    static public void push(FindContributors scope) {
	start();
        if (prover != null) {
            PrintStream ps = prover.subProcessToStream();
            ps.print("\n(BG_PUSH ");
            escjava.backpred.BackPred.genTypeBackPred(scope, ps);
            ps.println(")");
            prover.sendCommands("");
	    savedScope = scope;
	    status = PUSHED;
        }
    }

    synchronized
    static public Enumeration prove(Expr vc, FindContributors scope) {
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
	    prover.startProve();
	    VcToString.compute(vc, prover.subProcessToStream());
	    Enumeration en = prover.streamProve();
	    if (listener != null) listener.stateChanged(1);
	    return en;
	} catch (FatalError e) {
	    died();
	    return null;
	}
    }

    synchronized
    static public void pop() {
        if (prover != null)
            prover.sendCommand("(BG_POP)");
	savedScope = null;
	status = STARTED;
    }

    /**
     * Our Simplify instance.
     */
    //-@ monitored
    public static Simplify prover;
	//@ private invariant isStarted ==> prover != null;

}

	
