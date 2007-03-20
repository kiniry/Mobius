package escjava.dfa.daganalysis;

import java.io.PrintStream;
import java.util.Enumeration;

import javafe.ast.Expr;
import javafe.ast.ExprVec;
import javafe.ast.PrettyPrint;
import javafe.util.Assert;
import javafe.util.FatalError;
import escjava.ProverManager;
import escjava.ast.EscPrettyPrint;
import escjava.ast.GuardedCmd;
import escjava.prover.SimplifyOutput;
import escjava.translate.GC;
import escjava.translate.VcToString;

public class Simplifier {

    public static Expr simplify(Expr e) {
        return (Expr) e.clone();
    }


    public static boolean isFalse(Expr e) {
        // optimize for boolean literals
        if (GC.isBooleanLiteral(e, true))
            return false;
        if (GC.isBooleanLiteral(e, false))
            return true;

        // negate
        Expr neg = GC.not(e);

        /* DBG
        printExpr("Running prover on:", e);
        System.out.println();*/

        // run prover on the negated formula
        return runProver(neg);
    }


    // TODO: check this works as intended: should return true if simplify says
    // [e] is valid
    public static boolean runProver(Expr e) {
        boolean queryValid = false;
        try {
            PrintStream ps = ProverManager.prover().subProcessToStream();
            ProverManager.prover().startProve();
            VcToString.compute(e, ps);
            Enumeration results = ProverManager.prover().streamProve();
            queryValid = processSimplifyOutput(results);
        } catch (FatalError exc) {
            AlgebraUtils.printExpression("Seems like prover has died on", e);
            //exc.printStackTrace();
            ProverManager.kill(); // killing the prover process
            System.out.println("Killed");
            ProverManager.start(); // restarting the prover (might be unnecessary as ProverManager.prover() calls start)
            System.out.println("Started");
                     
        }
        return queryValid;
    }

    // Used when problems with Simplify encountered
    static String simplifyOutputKindToString(int kind) {
        switch (kind) {
        case SimplifyOutput.VALID:
            return "valid";
        case SimplifyOutput.COUNTEREXAMPLE:
            return "counterexample";
        case SimplifyOutput.INVALID:
            return "invalid";
        case SimplifyOutput.UNKNOWN:
            return "unknown";
        case SimplifyOutput.COMMENT:
            return "comment";
        case SimplifyOutput.EXCEEDED_PROVER_KILL_TIME:
            return "EXCEEDED_PROVER_KILL_TIME";
        case SimplifyOutput.EXCEEDED_PROVER_KILL_ITER:
            return "EXCEEDED_PROVER_KILL_ITER";
        case SimplifyOutput.REACHED_CC_LIMIT:
            return "REACHED_CC_LIMIT";
        case SimplifyOutput.EXCEEDED_PROVER_SUBGOAL_KILL_TIME:
            return "EXCEEDED_PROVER_SUBGOAL_KILL_TIME";
        case SimplifyOutput.EXCEEDED_PROVER_SUBGOAL_KILL_ITER:
            return "EXCEEDED_PROVER_SUBGOAL_KILL_ITER";
        case SimplifyOutput.WARNING_TRIGGERLESS_QUANT:
            return "WARNING_TRIGGERLESS_QUANT";
        default:
            return "Undefined";
        }
    }

    static boolean processSimplifyOutput(Enumeration results) {
        boolean valid = false;
        while (results.hasMoreElements()) {
            SimplifyOutput so = (SimplifyOutput) results.nextElement();

            int outputKind = so.getKind();
            switch (outputKind) {
            case SimplifyOutput.VALID: {
                valid = true;
                Assert.notFalse(!results.hasMoreElements());
                break;
            }

            case SimplifyOutput.COUNTEREXAMPLE:
                valid = false;
                break;

            case SimplifyOutput.INVALID:
                valid = false;
                break;

            case SimplifyOutput.UNKNOWN:
            case SimplifyOutput.COMMENT:
            case SimplifyOutput.EXCEEDED_PROVER_KILL_TIME:
            case SimplifyOutput.EXCEEDED_PROVER_KILL_ITER:
            case SimplifyOutput.REACHED_CC_LIMIT:
            case SimplifyOutput.EXCEEDED_PROVER_SUBGOAL_KILL_TIME:
            case SimplifyOutput.EXCEEDED_PROVER_SUBGOAL_KILL_ITER:
            case SimplifyOutput.WARNING_TRIGGERLESS_QUANT:
                System.err.println("Problems with Simplify: "
                        + simplifyOutputKindToString(outputKind));
                break;

            default:
                Assert.fail("unexpected type of Simplify output");
                break;
            }
        }

        return valid;
    }


    /* =========== DBG ============ */
    public static void printExpr(String s, Expr e) {
        System.out.println(s);
        VcToString.computeTypeSpecific(e, System.out);
        System.out.println();
    }

    public static void printGC(GuardedCmd gc) {
        ((EscPrettyPrint) PrettyPrint.inst).print(System.out, 0, gc);
        System.out.println();
    }

    public static void printlnExpr(Expr e) {
        VcToString.computeTypeSpecific(e, System.out);
        System.out.println();
    }

    public static void printlnExprVec(ExprVec evec) {
        System.out.print("[");
        for (int i = 0; i < evec.size(); i++) {
            printlnExpr(evec.elementAt(i));
            System.out.print(",");
        }
        System.out.println("]");
    }
}
