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

    final static private int NOTSTARTED = 0;
    final static private int STARTED = 1;
    final static private int PUSHED = 2;

	static private int status = 0;
	static private boolean isStarted = false;
	//@ invariant status != NOTSTARTED <==> isStarted;

	static private FindContributors savedScope = null;

	//@ ensures isStarted && prover != null;
	static public void start() {
	    if (isStarted) return;
            long startTime = java.lang.System.currentTimeMillis();
            prover = new Simplify();
            
            if (!Main.options().quiet)
                System.out.println("  Prover started:" + Main.timeUsed(startTime));

            escjava.backpred.BackPred.genUnivBackPred(prover.subProcessToStream());
            prover.sendCommands("");
	    isStarted = true;
	    status = STARTED;
	}

	static public Simplify prover() {
	    start();
	    return prover;
	}
	//@ ensures status == NOTSTARTED && prover == null;
	static public void kill() {
            if (prover != null) prover.close();
            prover = null;
	    isStarted = false;
	    status = NOTSTARTED;
	}

    static public void died() {
	if (prover != null) prover.close();
	prover = null;
	isStarted = false;
	status = NOTSTARTED;
    }

    static public void push(Expr vc) {
	PrintStream ps = prover.subProcessToStream();
	ps.print("\n(BG_PUSH ");
	VcToString.computePC(vc, ps);
	ps.println(")");
	prover.sendCommands("");
    }

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

    static public Enumeration prove(Expr vc) {
	if (savedScope != null && status != PUSHED) push(savedScope);
        prover.startProve();
        VcToString.compute(vc, prover.subProcessToStream());
	try {
	    return prover.streamProve();
	} catch (FatalError e) {
	    died();
	    return null;
	}
    }

    static public void pop() {
        if (prover != null)
            prover.sendCommand("(BG_POP)");
	savedScope = null;
	status = STARTED;
    }

    /**
     * Our Simplify instance.
     */
    public static Simplify prover;
	//@ invariant isStarted ==> prover != null;

}

	
