/**
 * @title Spec Tester
 * @description Creates tests for method specifications
 * @author Mikolas Janota
 */


package escjava.dfa.daganalysis;

import javafe.ast.*;
import escjava.ast.GuardedCmd;
import escjava.translate.InitialState;
import javafe.tc.TypeSig;
import escjava.sp.DSA;

import escjava.ast.ExprStmtPragma; // this is needed when creating assert false

// debug imports
import escjava.ast.EscPrettyPrint; 



/**
 * A class that encapsulated the function of constructing a test for a method's spec.
 * All this is quite experimental at the moment and the code below should be refactored (besides other things).
 *
 * @author Mikolas Janota
 */
public class SpecTester {

    /**
     * Construct a test for the given method.
     */
    public static  MethodDecl fabricateTest(MethodDecl r, TypeSig sig, InitialState initState) {
        StmtVec statements = StmtVec.make(); // statements in the body of the fabricated method

        // declare variables that will serve as arugments of the called method
        // the argument vector is created as well
        ExprVec callArgs = ExprVec.make();
        for (int i = 0;  i < r.args.size(); i++ ) {
            FormalParaDecl arg = r.args.elementAt(i);
            LocalVarDecl ti = LocalVarDecl.make(0, ModifierPragmaVec.make(),
                                                Identifier.intern("my_" + arg.id), arg.type,
                                                r.getStartLoc(),
                                                null,
                                                0);
            statements.addElement(VarDeclStmt.make(ti)); // declare var in statements
            callArgs.addElement(VariableAccess.make(ti.id, ti.locId, ti)); // add to args
        }


        // create method call
        ThisExpr thisExpr = ThisExpr.make(null, r.getStartLoc());
        ExprObjectDesignator thisOD = ExprObjectDesignator.make(r.getStartLoc(), thisExpr);
        MethodInvocation mi = MethodInvocation.make(thisOD, r.id(), null, r.getStartLoc(), r.getStartLoc(), callArgs);
        mi.decl = (MethodDecl) r;
        EvalStmt call = EvalStmt.make(mi);

        // add call to the statements
        statements.addElement(call); 

        // stick and assert false after the call
        statements.addElement(createAssertFalse(r.getStartLoc()));

        // create the whole testing method
        BlockStmt body = BlockStmt.make(statements, r.getStartLoc(), r.getStartLoc());
        MethodDecl fr =  MethodDecl.make(4194304, 
                                         null, 
                                         null, 
                                         FormalParaDeclVec.make(), 
                                         TypeNameVec.make(),
                                         body, 
                                         r.getStartLoc(), r.getStartLoc(), r.getStartLoc(), r.getStartLoc(), 
                                         Identifier.intern(r.id + "_testingMethod"),
                                         JavafePrimitiveType.make(TagConstants.VOIDTYPE, r.getStartLoc()),
                                         r.getStartLoc());

        // debug
        //    System.err.println("fabricated method: " + fr);

        fr.setParent(r.getParent());
        return fr;
    }



    /**
     * Run reachability analysis on the test created by <code>fabricateTest</code>.
     *
     * @param gc a guarded command, gets turned to DSA 
     */
    public static void runReachability(GuardedCmd gc) {
        // debug
        //         System.out.println("--- Fabricated GC ----");
        //         ((EscPrettyPrint)PrettyPrint.inst).print(System.out, 0, bodyGC);

         GuardedCmd bodyDSA = DSA.dsa(gc);
        // debug
        // System.out.println("\n --- Fabricated DSA ----");
        //                ((EscPrettyPrint)PrettyPrint.inst).print(System.out, 0, bodyDSA);

       // run reachability analyzis on the resulting DSA
       ReachabilityAnalysis.analyze(bodyDSA);
       //processRoutineDecl(fr, sig, initState);
    }

    private static  ExprStmtPragma createAssertFalse(int loc) {
        LiteralExpr falseLit = LiteralExpr.make(TagConstants.BOOLEANLIT, Boolean.FALSE, loc);
        javafe.tc.FlowInsensitiveChecks.setType(falseLit, JavafePrimitiveType.make(TagConstants.BOOLEANTYPE, loc));
        return ExprStmtPragma.make(escjava.ast.TagConstants.ASSERT, falseLit, null, loc);
    }

}