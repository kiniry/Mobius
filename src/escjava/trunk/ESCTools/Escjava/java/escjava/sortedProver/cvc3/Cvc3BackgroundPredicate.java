package escjava.sortedProver.cvc3;

import escjava.sortedProver.NodeBuilder.*;
import escjava.sortedProver.EscNodeBuilder.*;

import cvc3.*;

public class Cvc3BackgroundPredicate {
    
    //
    /// debug
    //
    final static private boolean printQuery = false;


    public static void sendBackgroundPredicate(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	// ESCJ 8 is at:
	// ESCTools/docs/design-notes/escj08a.html
	
	// The following is merely Simplify's universal background predicate from:
	// ESCTools/Escjava/java/escjava/backpred/UnivBackPred.ax


	//; "Universal", or class-independent part, of the background predicate

	//; === ESCJ 8: Section 0.4
	sendBPMaps(prover, builder);
	//; === ESCJ 8: Section 1.1
	sendBPSubTyping(prover, builder);
	//; === ESCJ 8: Section 1.2
	sendBPAsChild(prover, builder); //:TODO: not needed?
	//; === ESCJ 8: Section 1.3
	sendBPArrayTypes(prover, builder); //:TODO: not needed?
	//; === ESCJ 8: Section 2.1
	sendBPCasting(prover, builder);
	//; === ESCJ 8: Section 2.2
	sendBPTypeBool(prover, builder);
	//; === ESCJ 8: Section 2.2.1
	sendBPTypeInt(prover, builder);
	//; === ESCJ 8: Section 2.3
	sendBPTypeOf(prover, builder);
	//; === ESCJ 8: Section 2.4
	sendBPTypeField(prover, builder);
	//; === ESCJ 8: Section 2.5
	sendBPTypeArray(prover, builder);
	//; === ESCJ 8: Section 3.0
	//; === ESCJ 8: Section 3.1
	//; === ESCJ 8: Section 3.2
	sendBPAllocation(prover, builder);
	//; === ESCJ 8: Section 4 
	sendBPLocking(prover, builder);
	//; === ESCJ 8: Section 5.0
	sendBPArrays(prover, builder);
	//; === ESCJ 8: Section 5.1
	sendBPArith(prover, builder);
	//; === ESCJ 8: Section 5.2
	sendBPPredRefl(prover, builder);
	sendBPStrings(prover, builder);
	sendBPIntegral(prover, builder);
	//; === ESCJ 8: Section 5.3
	sendBPCondRefl(prover, builder);
	//; === Implementation of nonnullelements; not in ESCJ 8 (yet?):
	sendBPArrayNonNull(prover, builder);
	//; === Axioms about classLiteral; not in ESCJ 8 (yet?):
	sendBPClassLiteral(prover, builder);
	//; === Axioms about properties of integral &, |, and /
	//; === A few floating point axioms - DRCok
	sendBPArithMore(prover, builder);
    }

    public static void sendBPMaps(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPMaps:");
	//; === ESCJ 8: Section 0.4
	//    
	//(BG_PUSH (FORALL (m i x) (EQ (select (store m i x) i) x)))
	//
	//(BG_PUSH (FORALL (m i j x) 
	//		 (IMPLIES (NEQ i j)
	//			  (EQ (select (store m i x) j)
	//			      (select m j)))))
	//
	//(BG_PUSH (FORALL (m i j k x)
	//                 (IMPLIES (OR (< k i) (< j k))
	//                          (EQ (select (unset m i j) k) (select m k)))))
	
	//:TODO: what does the unset axiom mean?
	// arbitrary changes to m from i to j?
	// test495/Stackcheck.checkConstructor() seems to be the only test case using unset
    }

    public static void sendBPSubTypingPrimitive(Cvc3Prover prover, Cvc3NodeBuilder builder, FnSymbol type) throws Cvc3Exception {
	QuantVar v0 = builder.registerQuantifiedVariable("t0", builder.sortType);
	SAny t0;
	SPred p, p0, p1;
	STerm[][] pats;
	QuantVar[] vars0;

	//(BG_PUSH (FORALL (t) (PATS (<: t %type%))
	//	(IMPLIES (<: t %type%) (EQ t %type%))))
	t0 = builder.buildFnCall(type, new SAny[] {});
	p0 = builder.buildPredCall(builder.symTypeLE, new SAny[]{ builder.buildQVarRef(v0), t0 });
	p1 = builder.buildAnyEQ(builder.buildQVarRef(v0), t0);
	pats = new STerm[1][];
	pats[0] = new STerm[] { p0 };
	vars0 = new QuantVar[]{ v0 };
	p = builder.buildForAll(vars0, builder.buildImplies(p0, p1), pats, null);
	prover.declareAxiom(p);

	//(BG_PUSH (FORALL (t) (PATS (<: %type% t))
	//	(IMPLIES (<: %type% t) (EQ t %type%))))
	t0 = builder.buildFnCall(type, new SAny[] {});
	p0 = builder.buildPredCall(builder.symTypeLE, new SAny[]{ t0, builder.buildQVarRef(v0) });
	p1 = builder.buildAnyEQ(builder.buildQVarRef(v0), t0);
	pats = new STerm[1][];
	pats[0] = new STerm[] { p0 };
	vars0 = new QuantVar[]{ v0 };
	p = builder.buildForAll(vars0, builder.buildImplies(p0, p1), pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPSubTyping(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPSubTyping:");
	//; === ESCJ 8: Section 1.1

	QuantVar v0 = builder.registerQuantifiedVariable("t0", builder.sortType);
	QuantVar v1 = builder.registerQuantifiedVariable("t1", builder.sortType);
	QuantVar v2 = builder.registerQuantifiedVariable("t2", builder.sortType);
	QuantVar[] vars0;
	SAny t0;
	STerm[][] pats;
	SPred p, p0, p1, p2;

	//
	//(DEFPRED (<: t0 t1))
	//

	//; <: reflexive
	//(BG_PUSH 
	//  (FORALL (t)
	//    (PATS (<: t t))
	//    (<: t t)))
	p0 = builder.buildPredCall(builder.symTypeLE, new SAny[] { builder.buildQVarRef(v0), builder.buildQVarRef(v0) });
	pats = new STerm[1][];
	pats[0] = new STerm[] { p0 };
	vars0 = new QuantVar[] { v0 };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);

	//; a special case, for which the above may not fire
	//
	//(BG_PUSH (<: |T_java.lang.Object| |T_java.lang.Object|))
	t0 = builder.buildFnCall(builder.symTObject, new SAny[] {});
	p = builder.buildPredCall(builder.symTypeLE, new SAny[] { t0, t0 });
	prover.declareAxiom(p);

	//
	//; <: transitive	
	//(BG_PUSH 
	//  (FORALL (t0 t1 t2)
	//    (PATS (MPAT (<: t0 t1) (<: t1 t2)))
	//    (IMPLIES (AND (<: t0 t1) (<: t1 t2))
	//      (<: t0 t2))))
        if (!builder.optBuiltinTrans) {
            p0 = builder.buildPredCall(builder.symTypeLE, new SAny[] { builder.buildQVarRef(v0), builder.buildQVarRef(v1) });
            p1 = builder.buildPredCall(builder.symTypeLE, new SAny[] { builder.buildQVarRef(v1), builder.buildQVarRef(v2) });
            p2 = builder.buildPredCall(builder.symTypeLE, new SAny[] { builder.buildQVarRef(v0), builder.buildQVarRef(v2) });
            pats = new STerm[1][];
            pats[0] = new STerm[] { p0, p1 };
            vars0 = new QuantVar[]{ v0, v1, v2 };
            p = builder.buildForAll(vars0, builder.buildImplies(builder.buildAnd(p0, p1), p2), pats, null);
            prover.declareAxiom(p);
        }

	//;anti-symmetry
	//(BG_PUSH
	// (FORALL
	//  (t0 t1)
	//  (PATS (MPAT (<: t0 t1) (<: t1 t0)))
	//  (IMPLIES (AND (<: t0 t1) (<: t1 t0)) (EQ t0 t1))))
	p0 = builder.buildPredCall(builder.symTypeLE, new SAny[]{ builder.buildQVarRef(v0), builder.buildQVarRef(v1) });
	p1 = builder.buildPredCall(builder.symTypeLE, new SAny[]{ builder.buildQVarRef(v1), builder.buildQVarRef(v0) });
	p2 = builder.buildAnyEQ(builder.buildQVarRef(v0), builder.buildQVarRef(v1));
	pats = new STerm[1][];
	pats[0] = new STerm[] { p0, p1 };
	vars0 = new QuantVar[]{ v0, v1 };
	p = builder.buildForAll(vars0, builder.buildImplies(builder.buildAnd(p0, p1), p2), pats, null);
	prover.declareAxiom(p);	

	//; primitive types are final
	//
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_boolean|))
	//	(IMPLIES (<: t |T_boolean|) (EQ t |T_boolean|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTBoolean);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_char|))
	//	(IMPLIES (<: t |T_char|) (EQ t |T_char|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTChar);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_byte|))
	//	(IMPLIES (<: t |T_byte|) (EQ t |T_byte|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTByte);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_short|))
	//	(IMPLIES (<: t |T_short|) (EQ t |T_short|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTShort);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_int|))
	//	(IMPLIES (<: t |T_int|) (EQ t |T_int|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTInt);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_long|))
	//	(IMPLIES (<: t |T_long|) (EQ t |T_long|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTLong);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_float|))
	//	(IMPLIES (<: t |T_float|) (EQ t |T_float|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTFloat);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_double|))
	//	(IMPLIES (<: t |T_double|) (EQ t |T_double|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTDouble);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_bigint|))
	//	(IMPLIES (<: t |T_bigint|) (EQ t |T_bigint|))))
	//:TODO: sendBPSubTypingPrimitive(prover, builder, builder.symTBigInt);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_real|))
	//	(IMPLIES (<: t |T_real|) (EQ t |T_real|))))
	//:TODO: sendBPSubTypingPrimitive(prover, builder, builder.symTReal);
	//(BG_PUSH (FORALL (t) (PATS (<: t |T_void|))
	//	(IMPLIES (<: t |T_void|) (EQ t |T_void|))))
	sendBPSubTypingPrimitive(prover, builder, builder.symTVoid);

	// :ALEX: already handled above

	//; (New as of 12 Dec 2000)
	//; primitive types have no proper supertypes
	//
	//(BG_PUSH (FORALL (t) (PATS (<: |T_boolean| t))
	//	(IMPLIES (<: |T_boolean| t) (EQ t |T_boolean|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_char| t))
	//	(IMPLIES (<: |T_char| t) (EQ t |T_char|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_byte| t))
	//	(IMPLIES (<: |T_byte| t) (EQ t |T_byte|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_short| t))
	//	(IMPLIES (<: |T_short| t) (EQ t |T_short|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_int| t))
	//	(IMPLIES (<: |T_int| t) (EQ t |T_int|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_long| t))
	//	(IMPLIES (<: |T_long| t) (EQ t |T_long|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_float| t))
	//	(IMPLIES (<: |T_float| t) (EQ t |T_float|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_double| t))
	//	(IMPLIES (<: |T_double| t) (EQ t |T_double|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_bigint| t))
	//	(IMPLIES (<: |T_bigint| t) (EQ t |T_bigint|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_real| t))
	//	(IMPLIES (<: |T_real| t) (EQ t |T_real|))))
	//(BG_PUSH (FORALL (t) (PATS (<: |T_void| t))
	//	(IMPLIES (<: |T_void| t) (EQ t |T_void|))))
    }

    public static void sendBPAsChild(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPAsChild:");
	//; === ESCJ 8: Section 1.2
	//
	//(BG_PUSH
	//  (FORALL (t0 t1 t2)
	//    (PATS (<: t0 (asChild t1 t2)))
	//    (IMPLIES
	//      (<: t0 (asChild t1 t2))
	//      (EQ (classDown t2 t0) (asChild t1 t2)))))
	QuantVar v0 = builder.registerQuantifiedVariable("t0", builder.sortType);
	QuantVar v1 = builder.registerQuantifiedVariable("t1", builder.sortType);
	QuantVar v2 = builder.registerQuantifiedVariable("t2", builder.sortType);
	SAny t0 = builder.buildFnCall(builder.symAsChild, new SAny[] { builder.buildQVarRef(v1), builder.buildQVarRef(v2) });
	SAny t1 = builder.buildFnCall(builder.symClassDown, new SAny[] { builder.buildQVarRef(v2), builder.buildQVarRef(v0) });
	SPred p0 = builder.buildPredCall(builder.symTypeLE, new SAny[] { builder.buildQVarRef(v0), t0 });
	//SPred p1 = builder.buildPredCall(builder.symTypeEQ, new SAny[] { t1, t0 });
	SPred p1 = builder.buildAnyEQ(t1, t0);
	STerm[][] pats = new STerm[1][];
	pats[0] = new STerm[] { p0 };
	QuantVar[] vars0 = new QuantVar[] { v0, v1, v2 };
	SPred p = builder.buildForAll(vars0, builder.buildImplies(p0, p1), pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPArrayTypes(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPArrayTypes:");
	//; === ESCJ 8: Section 1.3

	QuantVar v0 = builder.registerQuantifiedVariable("t0", builder.sortType);
	QuantVar v1 = builder.registerQuantifiedVariable("t1", builder.sortType);
	SAny t0, t1, t2;
	QuantVar[] vars0;
	STerm[][] pats;
	SPred p, p0, p1, p2;
	//; new
	//
	//(BG_PUSH 
	//  (<: |T_java.lang.Cloneable| |T_java.lang.Object|))
	t0 = builder.buildFnCall(builder.symTCloneable, new SAny[] {});
	t1 = builder.buildFnCall(builder.symTObject, new SAny[] {});
	p = builder.buildPredCall(builder.symTypeLE, new SAny[] { t0, t1 });
	prover.declareAxiom(p);
	//
	//(BG_PUSH
	//  (FORALL (t)
	//    (PATS (|_array| t))
	//    (<: (|_array| t) |T_java.lang.Cloneable|)))
	t0 = builder.buildFnCall(builder.symArray, new SAny[] { builder.buildQVarRef(v0) });
	t1 = builder.buildFnCall(builder.symTCloneable, new SAny[] {});
	p0 = builder.buildPredCall(builder.symTypeLE, new SAny[] { t0, t1 });
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { v0 };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);
	//    
	//(BG_PUSH
	//  (FORALL (t)
	//    (PATS (elemtype (|_array| t)))
	//    (EQ (elemtype (|_array| t)) t)))
	t0 = builder.buildFnCall(builder.symArray, new SAny[] { builder.buildQVarRef(v0) });
	t1 = builder.buildFnCall(builder.symElemType, new SAny[] { t0 });
	p0 = builder.buildAnyEQ(t1, builder.buildQVarRef(v0));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t1 };
	vars0 = new QuantVar[] { v0 };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);
	//
	//(BG_PUSH
	//  (FORALL (t0 t1) 
	//    (PATS (<: t0 (|_array| t1)))
	//    (IFF (<: t0 (|_array| t1))
	//      (AND
	//	(EQ t0 (|_array| (elemtype t0)))
	//	(<: (elemtype t0) t1)))))
	t0 = builder.buildFnCall(builder.symArray, new SAny[] { builder.buildQVarRef(v1) });
	t1 = builder.buildFnCall(builder.symElemType, new SAny[] { builder.buildQVarRef(v0) });
	t2 = builder.buildFnCall(builder.symArray, new SAny[] { t1 });
	p0 = builder.buildPredCall(builder.symTypeLE, new SAny[] { builder.buildQVarRef(v0), t0 });
	p1 = builder.buildAnyEQ(builder.buildQVarRef(v0), t2);
	p2 = builder.buildPredCall(builder.symTypeLE, new SAny[] { t1, builder.buildQVarRef(v1) });
	pats = new STerm[1][];
	pats[0] = new STerm[] { p0 };
	vars0 = new QuantVar[] { v0, v1 };
	p = builder.buildForAll(vars0, builder.buildIff(p0, builder.buildAnd(p1, p2)), pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPCasting(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPCasting:");
	//; === ESCJ 8: Section 2.1

	QuantVar v0 = builder.registerQuantifiedVariable("x0", builder.sortValue);
	QuantVar v1 = builder.registerQuantifiedVariable("t0", builder.sortType);
	SAny t0, t1, t2;
	QuantVar[] vars0;
	STerm[][] pats;
	SPred p, p0, p1, p2;

	//(DEFPRED (is x t))
	//
	//(BG_PUSH
	// (FORALL (x t)
	//	 (PATS (cast x t))
	//	 (is (cast x t) t)))
	t0 = builder.buildFnCall(builder.symCast, new SAny[] { builder.buildQVarRef(v0), builder.buildQVarRef(v1) });
	p0 = builder.buildPredCall(builder.symIs, new SAny[] { t0, builder.buildQVarRef(v1) });
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { v0, v1 };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);
	//(BG_PUSH
	// (FORALL (x t)
	//	 (PATS (cast x t))
	//	 (IMPLIES (is x t) (EQ (cast x t) x))))
	t0 = builder.buildFnCall(builder.symCast, new SAny[] { builder.buildQVarRef(v0), builder.buildQVarRef(v1) });
	p0 = builder.buildPredCall(builder.symIs, new SAny[] { builder.buildQVarRef(v0), builder.buildQVarRef(v1) });
	p1 = builder.buildAnyEQ(t0, builder.buildQVarRef(v0));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { v0, v1 };
	p = builder.buildForAll(vars0, builder.buildImplies(p0, p1), pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPTypeBool(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPTypeBool:");
	//; === ESCJ 8: Section 2.2
	//
	//(BG_PUSH (DISTINCT |bool$false| |@true|))
    }

    public static void sendBPTypeInt(Cvc3Prover prover, Cvc3NodeBuilder builder, FnSymbol type, SInt lb, SInt ub) throws Cvc3Exception {
	//; === ESCJ 8: Section 2.2.1

	QuantVar v0 = builder.registerQuantifiedVariable("x0", builder.sortValue);
	Cvc3Int i0 = (Cvc3Int) builder.wrapExpr(((Cvc3Any)builder.buildQVarRef(v0)).getExpr(), builder.sortInt);
	QuantVar[] vars0;
	STerm[][] pats;
	SPred p, p0, p1, p2;

	//(BG_PUSH (FORALL (x) 
	//	   (PATS (is x %type%)) 
	//	   (IFF (is x %type%) (AND (<= %lb% x) (<= x %ub%)))))
	p0 = builder.buildPredCall(builder.symIs, new SAny[] { builder.buildQVarRef(v0), builder.buildFnCall(type, new SAny[] {}) });
	p1 = builder.buildIntPred(builder.predLE, lb, i0);
	p2 = builder.buildIntPred(builder.predLE, i0, ub);
	pats = new STerm[1][];
	pats[0] = new STerm[] { p0 };
	vars0 = new QuantVar[] { v0 };
	p = builder.buildForAll(vars0, builder.buildIff(p0, builder.buildAnd(p1, p2)), pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPTypeInt(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPTypeInt:");
	//:TODO: are symbolic values for intFirst, ... used anywhere?
	// we are assuming that not, not using them in any axiom,
	// and putting assertions in Cvc3NodeBuilder to check that they don't occur.

	//; === ESCJ 8: Section 2.2.1
	//
	//(BG_PUSH (FORALL (x) 
	//	   (PATS (is x |T_char|)) 
	//	   (IFF (is x |T_char|) (AND (<= 0 x) (<= x 65535)))))
	sendBPTypeInt(prover, builder, builder.symTChar, builder.buildInt(0), builder.buildInt(65535));
	//(BG_PUSH (FORALL (x)
	//	   (PATS (is x |T_byte|))
	//	   (IFF (is x |T_byte|) (AND (<= -128 x) (<= x 127)))))
	sendBPTypeInt(prover, builder, builder.symTByte, builder.buildInt(Byte.MIN_VALUE), builder.buildInt(Byte.MAX_VALUE));
	//(BG_PUSH (FORALL (x) 
	//	   (PATS (is x |T_short|))
	//	   (IFF (is x |T_short|) (AND (<= -32768 x) (<= x 32767)))))
	sendBPTypeInt(prover, builder, builder.symTShort, builder.buildInt(Short.MIN_VALUE), builder.buildInt(Short.MAX_VALUE));
	//(BG_PUSH (FORALL (x) 
	//	   (PATS (is x |T_int|))
	//	   (IFF (is x |T_int|) (AND (<= intFirst x) (<= x intLast)))))
	//	sendBPTypeInt(prover, builder.symTInt, builder.buildInt(intFirst), builder.buildInt(intLast));
	sendBPTypeInt(prover, builder, builder.symTInt, builder.buildInt(Integer.MIN_VALUE), builder.buildInt(Integer.MAX_VALUE));
	//(BG_PUSH (FORALL (x) 
	//	   (PATS (is x |T_long|))
	//	   (IFF (is x |T_long|) (AND (<= longFirst x) (<= x longLast)))))
	//	sendBPTypeInt(prover, builder.symTLong, builder.buildInt(longFirst), builder.buildInt(longLast));
	sendBPTypeInt(prover, builder, builder.symTLong, builder.buildInt(Long.MIN_VALUE), builder.buildInt(Long.MAX_VALUE));
	//(BG_PUSH (< longFirst intFirst))
	//(BG_PUSH (< intFirst -1000000))
	//(BG_PUSH (< 1000000 intLast))
	//(BG_PUSH (< intLast longLast))
	//
	//; == Defining bigint
	//(BG_PUSH (EQ |T_bigint| |T_long|))  ; FIXME - change this eventually
 	SAny t0 = builder.buildFnCall(builder.symTBigInt, new SAny[] {});
 	SAny t1 = builder.buildFnCall(builder.symTLong, new SAny[] {});
 	SPred p = builder.buildAnyEQ(t0, t1);
 	prover.declareAxiom(p);
    }

    public static void sendBPTypeOf(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPTypeOf:");
	//
	//; === Define typeof for primitive types - DRCok
	//; Removed because numeric values can be more than one type -
	//; e.g. is(0,|T_byte|) and is(0,|T_int|) are both true
	//; Thus these axioms introduce an inconsistency.
	//; Pointed out by Michal Moskal 2/2006.
	//
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   (IFF (is x |T_int|) (EQ (typeof x) |T_int|))
	//;    ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_short|))
	//;	   (IFF (is x |T_short|) (EQ (typeof x) |T_short|))
	//;    ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_long|))
	//;	   (IFF (is x |T_long|) (EQ (typeof x) |T_long|))
	//;     ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_byte|))
	//;	   (IFF (is x |T_byte|) (EQ (typeof x) |T_byte|))
	//;     ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_char|))
	//;	   (IFF (is x |T_char|) (EQ (typeof x) |T_char|))
	//;     ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_boolean|))
	//;	   (IFF (is x |T_boolean|) (EQ (typeof x) |T_boolean|))
	//;     ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_double|))
	//;	   (IFF (is x |T_double|) (EQ (typeof x) |T_double|))
	//;     ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_float|))
	//;	   (IFF (is x |T_float|) (EQ (typeof x) |T_float|))
	//;     ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_real|))
	//;	   (IFF (is x |T_real|) (EQ (typeof x) |T_real|))
	//;     ))
	//;(BG_PUSH (FORALL (x) 
	//;	   (PATS (typeof x))
	//;	   ;(PATS (is x |T_bigint|))
	//;	   (IFF (is x |T_bigint|) (EQ (typeof x) |T_bigint|))
	//;     ))
	//
	//;; Not sure why (or if) this should be here
	//(BG_PUSH (FORALL (x) 
	//	   (PATS (typeof x))
	//	   ;(PATS (is x |T_void|))
	//	   (IFF (is x |T_void|) (EQ (typeof x) |T_void|))
	//     ))
	// :TODO:
	//
	//; === ESCJ 8: Section 2.3
	//      
	//(BG_PUSH
	// (FORALL (x t)
	//	 (PATS (MPAT (<: t |T_java.lang.Object|) (is x t)))
	//	 (IMPLIES (<: t |T_java.lang.Object|)
	//		  (IFF (is x t)
	//		       (OR (EQ x null) (<: (typeof x) t))))))
	QuantVar v0 = builder.registerQuantifiedVariable("x0", builder.sortValue);
	QuantVar v1 = builder.registerQuantifiedVariable("t0", builder.sortType);
	SAny t0 = builder.buildFnCall(builder.symTypeOf, new SAny[] { builder.buildQVarRef(v0) });
	SPred p0 = builder.buildPredCall(builder.symTypeLE, new SAny[] { builder.buildQVarRef(v1), builder.buildFnCall(builder.symTObject, new SAny[] {}) });
	SPred p1 = builder.buildPredCall(builder.symIs, new SAny[] { builder.buildQVarRef(v0), builder.buildQVarRef(v1) });
	SPred p2 = builder.buildAnyEQ(builder.buildQVarRef(v0), builder.buildNull());
	SPred p3 = builder.buildPredCall(builder.symTypeLE, new SAny[] { t0, builder.buildQVarRef(v1) });
	
	// :TODO: this multi-trigger not effective in cvc3, use single trigger in addition
	// p0 can not be used, as it doesn't refer to all quantified variables
	STerm[][] pats = new STerm[2][];
	pats[0] = new STerm[] { p0, p1 };
	pats[1] = new STerm[] { p1 };

	QuantVar[] vars0 = new QuantVar[] { v0, v1 };
	SPred p = builder.buildForAll(vars0, builder.buildImplies(p0, builder.buildIff(p1, builder.buildOr(p2, p3))), pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPTypeFieldX(Cvc3Prover prover, Cvc3NodeBuilder builder, Sort field) throws Cvc3Exception {
	QuantVar vf = builder.registerQuantifiedVariable("f0", field);
	QuantVar vt = builder.registerQuantifiedVariable("t0", builder.sortType);
	QuantVar vx = builder.registerQuantifiedVariable("x0", builder.sortRef);
	SMap t0 = (SMap) builder.buildFnCall(builder.symAsField, new SAny[] { builder.buildQVarRef(vf), builder.buildQVarRef(vt) });
	SAny t1 = builder.buildSelect(t0, (SValue)builder.buildQVarRef(vx));
	SPred p0 = builder.buildPredCall(builder.symIs, new SAny[] { t1, builder.buildQVarRef(vt) });
	STerm[][] pats = new STerm[1][];
	pats[0] = new STerm[] { t1 };
	QuantVar[] vars0 = new QuantVar[] { vf, vt, vx };
	SPred p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);
	
    }

    public static void sendBPTypeField(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPTypeField:");
	//; === ESCJ 8: Section 2.4
	//
	//(BG_PUSH
	// (FORALL (f t x) (PATS (select (asField f t) x))
	//	 (is (select (asField f t) x) t)))
	//    }
	sendBPTypeFieldX(prover, builder, builder.sortBoolField);
	sendBPTypeFieldX(prover, builder, builder.sortIntField);
	sendBPTypeFieldX(prover, builder, builder.sortRealField);
	sendBPTypeFieldX(prover, builder, builder.sortRefField);
    }

    public static void sendBPTypeArray(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPTypeArray:");
	//; === ESCJ 8: Section 2.5
	//
	//(BG_PUSH
	// (FORALL (e a i) (PATS (select (select (asElems e) a) i))
	//	 (is (select (select (asElems e) a) i)
	//	     (elemtype (typeof a)))))
	QuantVar ve = builder.registerQuantifiedVariable("e0", builder.sortElems);
	QuantVar va = builder.registerQuantifiedVariable("a0", builder.sortRef);
	QuantVar vi = builder.registerQuantifiedVariable("i0", builder.sortInt);
	SMap t0 = (SMap) builder.buildFnCall(builder.symAsElems, new SAny[] { builder.buildQVarRef(ve) });
	SMap t1 = (SMap) builder.buildSelect(t0, (SValue)builder.buildQVarRef(va));
	SAny t2 = builder.buildSelect(t1, (SValue)builder.buildQVarRef(vi));
	SAny t3 = builder.buildFnCall(builder.symTypeOf, new SAny[] { builder.buildQVarRef(va) });
	SAny t4 = builder.buildFnCall(builder.symElemType, new SAny[] { t3 });
	SPred p0 = builder.buildPredCall(builder.symIs, new SAny[] { t2, t4 });
	STerm[][] pats = new STerm[1][];
	pats[0] = new STerm[] { t2 };
	QuantVar[] vars0 = new QuantVar[] { ve, va, vi };
	SPred p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPAllocation(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPAllocation:");
	//; === ESCJ 8: Section 3.0
	QuantVar vx = builder.registerQuantifiedVariable("x", builder.sortRef);
	QuantVar va = builder.registerQuantifiedVariable("a", builder.sortTime);
	QuantVar va0 = builder.registerQuantifiedVariable("a0", builder.sortTime);
	QuantVar vf = builder.registerQuantifiedVariable("f", builder.sortRefField);
	QuantVar ve = builder.registerQuantifiedVariable("e0", builder.sortElems);
	QuantVar vi = builder.registerQuantifiedVariable("i0", builder.sortInt);
	QuantVar[] vars0;
	STerm[][] pats;
	SAny t0, t1, t2;
	SPred p, p0, p1, p2;

	//(DEFPRED (isAllocated x a0) (< (vAllocTime x) a0))
        if (!builder.optIsallocated) {

            t0 = builder.buildFnCall(builder.symvAllocTime, new SAny[] { builder.buildQVarRef(vx) });
            p0 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { builder.buildQVarRef(vx), builder.buildQVarRef(va0) });
            p1 = builder.buildIntPred(builder.predLT, (SInt)t0, (SInt)builder.buildQVarRef(va0));
            vars0 = new QuantVar[] { vx, va0 };
            p = builder.buildForAll(vars0, builder.buildIff(p0, p1), null, null);
            prover.declareAxiom(p);
        }

	// handled by replacement in buildPredCall

	//; === ESCJ 8: Section 3.1
	//
	//(BG_PUSH
	// (FORALL (x f a0) (PATS (isAllocated (select f x) a0))
	//	 (IMPLIES (AND (< (fClosedTime f) a0)
	//		       (isAllocated x a0))
	//		  (isAllocated (select f x) a0))))

	// :TODO: allocation makes only sense for ref fields
	//sendBPFClosedTimeX(prover, builder, builder.sortBoolField);
	//sendBPFClosedTimeX(prover, builder, builder.sortIntField);
	//sendBPFClosedTimeX(prover, builder, builder.sortRealField);
	// sendBPFClosedTimeX(prover, builder, builder.sortRefField);
	t0 = builder.buildFnCall(builder.symFClosedTime, new SAny[] { builder.buildQVarRef(vf) });
	t1 = builder.buildSelect((SMap)builder.buildQVarRef(vf), (SValue)builder.buildQVarRef(vx));
	p0 = builder.buildIntPred(builder.predLT, (SInt)t0, (SInt)builder.buildQVarRef(va0));
	p1 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { builder.buildQVarRef(vx), builder.buildQVarRef(va0) });
	p2 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { t1, builder.buildQVarRef(va0) });
	pats = new STerm[1][];
	pats[0] = new STerm[] { p2 };
	vars0 = new QuantVar[] { vx, vf, va0 };
	p = builder.buildForAll(vars0, builder.buildImplies(builder.buildAnd(p0, p1), p2), pats, null);
	prover.declareAxiom(p);
	//
	//; === ESCJ 8: Section 3.2
	//
	//(BG_PUSH
	// (FORALL (a e i a0) (PATS (isAllocated (select (select e a) i) a0))
	//	 (IMPLIES (AND (< (eClosedTime e) a0)
	//		       (isAllocated a a0))
	//		  (isAllocated (select (select e a) i) a0))))
	t0 = builder.buildFnCall(builder.symEClosedTime, new SAny[] { builder.buildQVarRef(ve) });
	t1 = builder.buildSelect((SMap)builder.buildQVarRef(ve), (SValue)builder.buildQVarRef(vx));
	t2 = builder.buildSelect((SMap)t1, (SValue)builder.buildQVarRef(vi));
	p0 = builder.buildIntPred(builder.predLT, (SInt)t0, (SInt)builder.buildQVarRef(va0));
	p1 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { builder.buildQVarRef(vx), builder.buildQVarRef(va0) });
	p2 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { t2, builder.buildQVarRef(va0) });
	pats = new STerm[1][];
	pats[0] = new STerm[] { p2 };
	vars0 = new QuantVar[] { vx, ve, vi, va0 };
	p = builder.buildForAll(vars0, builder.buildImplies(builder.buildAnd(p0, p1), p2), pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPLocking(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPLocking:");
	//; === ESCJ 8: Section 4 
	QuantVar vs = builder.registerQuantifiedVariable("s", builder.sortLockSet);
	QuantVar vl = builder.registerQuantifiedVariable("l", builder.sortLock);
	QuantVar[] vars0;
	STerm[][] pats;
	SAny t0, t1, t2;
	SPred p, p0, p1, p2, p3, p4;
	//
	//; max(lockset) is in lockset
	//
	//(BG_PUSH
	// (FORALL (S)
	//  (PATS (select (asLockSet S) (max (asLockSet S))))
	//  (EQ
	//   (select (asLockSet S) (max (asLockSet S)))
	//   |@true|)))
	t0 = builder.buildFnCall(builder.symAsLockSet, new SAny[] { builder.buildQVarRef(vs) });
	t1 = builder.buildFnCall(builder.symMax, new SAny[] { t0 });
	t2 = builder.buildSelect((SMap)t0, (SValue)t1);
	p0 = builder.buildAnyEQ(t2, builder.buildBool(true));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t2 };
	vars0 = new QuantVar[] { vs };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);
	//
	//; null is in lockset (not in ESCJ 8)
	//
	//(BG_PUSH
	// (FORALL (S)
	//  (PATS (asLockSet S))
	//  (EQ (select (asLockSet S) null) |@true|)))
	t0 = builder.buildFnCall(builder.symAsLockSet, new SAny[] { builder.buildQVarRef(vs) });
	t1 = builder.buildSelect((SMap)t0, builder.buildNull());
	p0 = builder.buildAnyEQ(t1, builder.buildBool(true));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vs };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);
	//
	//(DEFPRED (lockLE x y) (<= x y))

	// handled by replacement in buildPredCall
	
	//(DEFPRED (lockLT x y) (< x y))

	// handled by replacement in buildPredCall

	//; all locks in lockset are below max(lockset) (not in ESCJ 8)
	//
	//(BG_PUSH
	// (FORALL (S mu)
	//  (IMPLIES
	//   (EQ (select (asLockSet S) mu) |@true|)
	//   (lockLE mu (max (asLockSet S))))))
	t0 = builder.buildFnCall(builder.symAsLockSet, new SAny[] { builder.buildQVarRef(vs) });
	t1 = builder.buildSelect((SMap)t0, (SValue)builder.buildQVarRef(vl));
	t2 = builder.buildFnCall(builder.symMax, new SAny[] { t0 });
	p0 = builder.buildAnyEQ(t1, builder.buildBool(true));
	p1 = builder.buildPredCall(builder.symLockLE, new SAny[] { builder.buildQVarRef(vl), t2 });
	vars0 = new QuantVar[] { vs, vl };
	p = builder.buildForAll(vars0, builder.buildImplies(p0, p1), null, null);
	prover.declareAxiom(p);
	//
	//; null precedes all objects in locking order (not in ESCJ 8)
	//
	//(BG_PUSH
	//  (FORALL (x)
	//    (PATS (lockLE null x) (lockLT null x) (lockLE x null) (lockLT x null))
	//    (IMPLIES
	//      (<: (typeof x) |T_java.lang.Object|)
	//      (lockLE null x))))
	t0 = builder.buildFnCall(builder.symTypeOf, new SAny[] { builder.buildQVarRef(vl) });
	p0 = builder.buildPredCall(builder.symTypeLE, new SAny[] { t0, builder.buildFnCall(builder.symTObject, new SAny[] {}) });
	p1 = builder.buildPredCall(builder.symLockLE, new SAny[] { builder.buildNull(), builder.buildQVarRef(vl) });
	p2 = builder.buildPredCall(builder.symLockLT, new SAny[] { builder.buildNull(), builder.buildQVarRef(vl) });
	p3 = builder.buildPredCall(builder.symLockLE, new SAny[] { builder.buildQVarRef(vl), builder.buildNull() });
	p4 = builder.buildPredCall(builder.symLockLT, new SAny[] { builder.buildQVarRef(vl), builder.buildNull() });
	pats = new STerm[4][];
	pats[0] = new STerm[] { p1 };
	pats[1] = new STerm[] { p2 };
	pats[2] = new STerm[] { p3 };
	pats[3] = new STerm[] { p4 };
	vars0 = new QuantVar[] { vl };
	p = builder.buildForAll(vars0, builder.buildImplies(p0, p1), pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPArrays(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPArrays:");
	//; === ESCJ 8: Section 5.0
	QuantVar va = builder.registerQuantifiedVariable("a", builder.sortArray);
	QuantVar va0 = builder.registerQuantifiedVariable("a0", builder.sortTime);
	QuantVar vb0 = builder.registerQuantifiedVariable("b0", builder.sortTime);
	QuantVar ve = builder.registerQuantifiedVariable("e", builder.sortElems);
	QuantVar vi = builder.registerQuantifiedVariable("i", builder.sortInt);
	QuantVar vn = builder.registerQuantifiedVariable("n", builder.sortInt);
	QuantVar vs = builder.registerQuantifiedVariable("s", builder.sortShape);
	QuantVar vt = builder.registerQuantifiedVariable("t", builder.sortType);
	QuantVar vv = builder.registerQuantifiedVariable("v", builder.sortValue);
	QuantVar[] vars0;
	STerm[][] pats;
	SAny t0, t1, t2, t3, t4;
	SPred p, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9;
	//
	//(BG_PUSH
	// (FORALL (a) 
	//	 (PATS (arrayLength a))
	//	 (AND (<= 0 (arrayLength a))
	//	      (is (arrayLength a) |T_int|))))
	//:TODO: can we get rid of 2nd conjunct?
	t0 = builder.buildFnCall(builder.symArrayLength, new SAny[] { builder.buildQVarRef(va) });
	p0 = builder.buildIntPred(builder.predLE, builder.buildInt(0), (SInt)t0);
	p1 = builder.buildPredCall(builder.symIs, new SAny[] { t0, builder.buildFnCall(builder.symTInt, new SAny[] {}) });
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { va };
	p = builder.buildForAll(vars0, builder.buildAnd(p0, p1), pats, null);
	prover.declareAxiom(p);
	//
	//(DEFPRED (arrayFresh a a0 b0 e s T v))
	//
	//(BG_PUSH
	//  (FORALL (a a0 b0 e n s T v)
	//    (PATS (arrayFresh a a0 b0 e (arrayShapeMore n s) T v))
	//    (IFF
	//      (arrayFresh a a0 b0 e (arrayShapeMore n s) T v)
	//      (AND
	//	(<= a0 (vAllocTime a))
	//	(isAllocated a b0)
	//	(NEQ a null)
	//	(EQ (typeof a) T)
	//	(EQ (arrayLength a) n)
	//	(FORALL (i)
	//	  (PATS (select (select e a) i))
	//	  (AND
	//	    (arrayFresh (select (select e a) i) a0 b0 e s (elemtype T) v)
	//	    (EQ (arrayParent (select (select e a) i)) a)
	//	    (EQ (arrayPosition (select (select e a) i)) i)))))))
	t0 = builder.buildFnCall(builder.symArrayShapeMore, new SAny[] { builder.buildQVarRef(vn), builder.buildQVarRef(vs) });
	t1 = builder.buildFnCall(builder.symvAllocTime, new SAny[] { builder.buildQVarRef(va) });
	t2 = builder.buildSelect((SMap)builder.buildQVarRef(ve), (SValue)builder.buildQVarRef(va));
	t3 = builder.buildSelect((SMap)t2, (SValue)builder.buildQVarRef(vi));
	t4 = builder.buildFnCall(builder.symElemType, new SAny[] { builder.buildQVarRef(vt) });
	p0 = builder.buildPredCall(builder.symArrayFresh, new SAny[]
	    { builder.buildQVarRef(va), builder.buildQVarRef(va0), builder.buildQVarRef(vb0), builder.buildQVarRef(ve),
	      t0, builder.buildQVarRef(vt), builder.buildQVarRef(vv) });
	p1 = builder.buildIntPred(builder.predLE, (SInt)builder.buildQVarRef(va0), (SInt)t1);
	p2 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { builder.buildQVarRef(va), builder.buildQVarRef(vb0) });
	p3 = builder.buildAnyNE(builder.buildQVarRef(va), builder.buildNull());
	p4 = builder.buildAnyEQ(builder.buildFnCall(builder.symTypeOf, new SAny[] { builder.buildQVarRef(va) }), builder.buildQVarRef(vt));
	p5 = builder.buildAnyEQ(builder.buildFnCall(builder.symArrayLength, new SAny[] { builder.buildQVarRef(va) }), builder.buildQVarRef(vn));
	p6 = builder.buildPredCall(builder.symArrayFresh, new SAny[]
	    { t3, builder.buildQVarRef(va0), builder.buildQVarRef(vb0), builder.buildQVarRef(ve),
	      builder.buildQVarRef(vs), t4, builder.buildQVarRef(vv) });
	p7 = builder.buildAnyEQ(builder.buildFnCall(builder.symArrayParent, new SAny[] { t3 }), builder.buildQVarRef(va));
	p8 = builder.buildAnyEQ(builder.buildFnCall(builder.symArrayPosition, new SAny[] { t3 }), builder.buildQVarRef(vi));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t3 };
	vars0 = new QuantVar[] { vi };
	p9 = builder.buildForAll(vars0, builder.buildAnd(new SPred[] { p6, p7, p8 } ), pats, null);
	pats[0] = new STerm[] { p0 };
	vars0 = new QuantVar[] { va, va0, vb0, ve, vn, vs, vt, vv };
	p = builder.buildForAll(vars0, builder.buildIff(p0, builder.buildAnd(new SPred[] { p1, p2, p3, p4, p5, p9 })), pats, null);
	prover.declareAxiom(p);
	//
	//(BG_PUSH
	//  (FORALL (a a0 b0 e n T v)
	//    (PATS (arrayFresh a a0 b0 e (arrayShapeOne n) T v))
	//    (IFF
	//      (arrayFresh a a0 b0 e (arrayShapeOne n) T v)
	//      (AND
	//	(<= a0 (vAllocTime a))
	//	(isAllocated a b0)
	//	(NEQ a null)
	//	(EQ (typeof a) T)
	//	(EQ (arrayLength a) n)
	//	(FORALL (i)
	//	  (PATS (select (select e a) i))
	//	  (AND
	//	    (EQ (select (select e a) i) v)))))))
	t0 = builder.buildFnCall(builder.symArrayShapeOne, new SAny[] { builder.buildQVarRef(vn) });
	t1 = builder.buildFnCall(builder.symvAllocTime, new SAny[] { builder.buildQVarRef(va) });
	t2 = builder.buildSelect((SMap)builder.buildQVarRef(ve), (SValue)builder.buildQVarRef(va));
	t3 = builder.buildSelect((SMap)t2, (SValue)builder.buildQVarRef(vi));
	p0 = builder.buildPredCall(builder.symArrayFresh, new SAny[]
	    { builder.buildQVarRef(va), builder.buildQVarRef(va0), builder.buildQVarRef(vb0), builder.buildQVarRef(ve),
	      t0, builder.buildQVarRef(vt), builder.buildQVarRef(vv) });
	p1 = builder.buildIntPred(builder.predLE, (SInt)builder.buildQVarRef(va0), (SInt)t1);
	p2 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { builder.buildQVarRef(va), builder.buildQVarRef(vb0) });
	p3 = builder.buildAnyNE(builder.buildQVarRef(va), builder.buildNull());
	p4 = builder.buildAnyEQ(builder.buildFnCall(builder.symTypeOf, new SAny[] { builder.buildQVarRef(va) }), builder.buildQVarRef(vt));
	p5 = builder.buildAnyEQ(builder.buildFnCall(builder.symArrayLength, new SAny[] { builder.buildQVarRef(va) }), builder.buildQVarRef(vn));
	p6 = builder.buildAnyEQ(t3, builder.buildQVarRef(vv));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t3 };
	vars0 = new QuantVar[] { vi };
	p7 = builder.buildForAll(vars0, p6, pats, null);
	pats[0] = new STerm[] { p0 };
	vars0 = new QuantVar[] { va, va0, vb0, ve, vn, vt, vv };
	p = builder.buildForAll(vars0, builder.buildIff(p0, builder.buildAnd(new SPred[] { p1, p2, p3, p4, p5, p7 })), pats, null);
	prover.declareAxiom(p);
	//
	//(BG_PUSH
	//  (FORALL (a0 b0 s T v e A)
	//    (PATS (arrayFresh A a0 b0 (asElems e) s T v))
	//    (IMPLIES
	//      (EQ A (arrayMake a0 b0 s T v))
	//      (arrayFresh A a0 b0 (asElems e) s T v)
	//    )
	//  )
	//)
	//
	//(BG_PUSH
	//  (FORALL (a0 b0 a1 b1 s1 s2 T1 T2 v)
	//    (PATS (MPAT (arrayMake a0 b0 s1 T1 v) (arrayMake a1 b1 s2 T2 v) ))
	//    (IMPLIES
	//	(EQ (arrayMake a0 b0 s1 T1 v) (arrayMake a1 b1 s2 T2 v))
	//	(AND (EQ b0 b1) (EQ T1 T2) (EQ s1 s2))
	//)))

	//:TODO: is arrayMake as a shortcut for arrayFresh used?

	//
	//; === code to ensure that (isNewArray x) ==> x has no invariants
	//
	//
	//; arrayType is distinct from all types with invariants (due to the
	//; generated type-distinctness axiom)
	//
	//(BG_PUSH
	//  (EQ arrayType (asChild arrayType |T_java.lang.Object|)))
	//
	//(BG_PUSH
	//   (FORALL (t)
	//      (PATS (|_array| t))
	//      (<: (|_array| t) arrayType)))
	//
	//(BG_PUSH
	//  (FORALL (s)
	//	  (PATS (isNewArray s))
	//	  (IMPLIES (EQ |@true| (isNewArray s))
	//		   (<: (typeof s) arrayType))))

	//:TODO: is arrayType used?
    }


    public static void sendBPArith(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPArith:");
	//; === ESCJ 8: Section 5.1

	QuantVar vi = builder.registerQuantifiedVariable("i", builder.sortInt);
	QuantVar vj = builder.registerQuantifiedVariable("j", builder.sortInt);
	SInt t0, t1, t2, t3;
	SPred p, p0, p1, p2, p3, p4, p5, p6;
	STerm[][] pats;
	QuantVar[] vars0;

	Cvc3Int qvi = (Cvc3Int) builder.wrapExpr(((Cvc3Any)builder.buildQVarRef(vi)).getExpr(), builder.sortInt);
	Cvc3Int qvj = (Cvc3Int) builder.wrapExpr(((Cvc3Any)builder.buildQVarRef(vj)).getExpr(), builder.sortInt);

	//; integralMod is the computer mod - the sign of the result is the sign of the
	//; first operand; it is not the mathematical mod, whose result is always positive
	//
	//; j != 0 ==> ((i/j)*j + (i%j) == i

	//(BG_PUSH
	// (FORALL (i j) (PATS (integralDiv i j) )
	// ;(FORALL (i j) (PATS (integralMod i j) (integralDiv i j))
	//	 (IMPLIES (NOT ( EQ j 0))
	//	 (EQ (+ (* (integralDiv i j) j) (integralMod i j))
	//	     i))))
	t0 = builder.buildIntFun(builder.funMOD, qvi, qvj);
	t1 = builder.buildIntFun(builder.funDIV, qvi, qvj);
	t2 = builder.buildIntFun(builder.funMUL, t1, qvj);
	t3 = builder.buildIntFun(builder.funADD, t2, t0);

	p0 = builder.buildAnyEQ(qvj, builder.buildInt(0));
	p1 = builder.buildNot(p0);
	p2 = builder.buildAnyEQ(t3, qvi);
	p3 = builder.buildImplies(p1, p2);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t1 };
	vars0 = new QuantVar[] { vi, vj };
	p = builder.buildForAll(vars0, p3, pats, null);
	prover.declareAxiom(p);
	

	//
	//;; FIXME? - If the above has a trigger of (integralMod i j) and the axiom
	//;; below is also included, then we get some inconsistency and a failure of
	//;; test 72
	//
	//; (i>=0 && j>0) ==> (i%j >= 0 && i%j < j)
	//(BG_PUSH
	// (FORALL (i j) (PATS (integralMod i j))
	//	 (IMPLIES (AND (< 0 j) (<= 0 i))
	//		  (AND (<= 0 (integralMod i j))
	//		       (< (integralMod i j) j)))))
	t0 = builder.buildIntFun(builder.funMOD, qvi, qvj);

	p0 = builder.buildIntPred(builder.predLT, builder.buildInt(0), qvj);
	p1 = builder.buildIntPred(builder.predLE, qvi, builder.buildInt(0));
	p2 = builder.buildAnd(p0, p1);

	p3 = builder.buildIntPred(builder.predLE, builder.buildInt(0), t0);
	p4 = builder.buildIntPred(builder.predLT, t0, qvj);
	p5 = builder.buildAnd(p3, p4);
	
	p6 = builder.buildImplies(p2, p5);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vi, vj };
	p = builder.buildForAll(vars0, p6, pats, null);
	prover.declareAxiom(p);


	//; (j != 0) ==> (0%j == 0)
	//(BG_PUSH
	// (FORALL (i j) (PATS (integralMod i j))
	//	 (IMPLIES (AND (NOT (EQ j 0)) (EQ i 0))
	//	  (EQ 0 (integralMod i j)))))
	t0 = builder.buildIntFun(builder.funMOD, qvi, qvj);

	p0 = builder.buildAnyEQ(qvj, builder.buildInt(0));
	p1 = builder.buildAnyEQ(qvi, builder.buildInt(0));
	p2 = builder.buildAnd(builder.buildNot(p0), p1);

	p3 = builder.buildAnyEQ(builder.buildInt(0), t0);
	
	p4 = builder.buildImplies(p2, p3);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vi, vj };
	p = builder.buildForAll(vars0, p4, pats, null);
	prover.declareAxiom(p);

	//
	//; (j != 0) ==> ((i>=0) ==> (i%j)>=0 ))
	//(BG_PUSH
	// (FORALL (i j) (PATS (integralMod i j))
	//	 (IMPLIES (NOT (EQ j 0)) 
	//	   (IMPLIES (<= 0 i) (<= 0 (integralMod i j))))))
	t0 = builder.buildIntFun(builder.funMOD, qvi, qvj);

	p0 = builder.buildNot(builder.buildAnyEQ(qvj, builder.buildInt(0)));

	p1 = builder.buildIntPred(builder.predLE, builder.buildInt(0), qvi);
	p2 = builder.buildIntPred(builder.predLE, builder.buildInt(0), t0);
	p3 = builder.buildImplies(p2, p3);

	p4 = builder.buildImplies(p0, p3);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vi, vj };
	p = builder.buildForAll(vars0, p4, pats, null);
	prover.declareAxiom(p);
	

	//; (j != 0) ==> ((i<=0) ==> (i%j)<=0 ))
	//(BG_PUSH
	// (FORALL (i j) (PATS (integralMod i j))
	//  (IMPLIES (NOT (EQ j 0)) 
	//		(IMPLIES (<= i 0) (<= (integralMod i j) 0)))))
	t0 = builder.buildIntFun(builder.funMOD, qvi, qvj);

	p0 = builder.buildNot(builder.buildAnyEQ(qvj, builder.buildInt(0)));

	p1 = builder.buildIntPred(builder.predLE, qvi, builder.buildInt(0));
	p2 = builder.buildIntPred(builder.predLE, t0, builder.buildInt(0));
	p3 = builder.buildImplies(p2, p3);

	p4 = builder.buildImplies(p0, p3);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vi, vj };
	p = builder.buildForAll(vars0, p4, pats, null);
	prover.declareAxiom(p);

	//; Only true for mathMod
	//;(BG_PUSH
	//; (FORALL (i j) 
	//;	 (PATS (integralMod (+ i j) j))
	//;	 (EQ (integralMod (+ i j) j) 
	//;	     (integralMod i j))))
	//;
	//;(BG_PUSH
	//; (FORALL (i j)
	//;	 (PATS (integralMod (+ j i) j))
	//;	 (EQ (integralMod (+ j i) j) 
	//;	     (integralMod i j))))
	//
	//; to prevent a matching loop
	// :TODO: needed?
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (* (integralDiv (* x y) y) y))
	//  (EQ (* (integralDiv (* x y) y) y) (* x y))))
    }

    public static void sendBPPredRefl(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPPredRefl:");
	//; === ESCJ 8: Section 5.2

	// type bool handled by cvc BitVector(1)
	// reflection by casting in Cvc3NodeBuilder

	//
	//(DEFPRED (boolAnd a b)
	//  (AND
	//    (EQ a |@true|) 
	//    (EQ b |@true|)))
	//
	//(DEFPRED (boolEq a b)
	//  (IFF
	//    (EQ a |@true|)
	//    (EQ b |@true|)))
	//
	//(DEFPRED (boolImplies a b)
	//  (IMPLIES
	//    (EQ a |@true|)
	//    (EQ b |@true|)))
	//    
	//(DEFPRED (boolNE a b)
	//  (NOT (IFF
	//	 (EQ a |@true|)
	//	 (EQ b |@true|))))
	//
	//(DEFPRED (boolNot a)
	//  (NOT (EQ a |@true|)))
	//
	//(DEFPRED (boolOr a b)
	//  (OR
	//    (EQ a |@true|)
	//    (EQ b |@true|)))
    }

    public static void sendBPStrings(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPStrings:");
	QuantVar va, va0, va1, vb, vi, vii, vk, vkk, vr, vs, vx, vy, vxx, vyy;
	SAny ta, ta0, ta1, tb, ti, tii, tk, tkk, tr, ts, tx, ty, txx, tyy, t0, t1, t2, t3;
	SPred p, p0, p1, p2, p3, p4, p5, p6;
	STerm[][] pats;
	QuantVar[] vars0;

	//; Axioms related to Strings - DRCok
	//
	//(DEFPRED (|interned:| s))
	//
	//(BG_PUSH
	//  (FORALL (i k)
	//    (PATS (|intern:| i k))
	//    (AND (NEQ (|intern:| i k) null)
	//         (EQ (typeof (|intern:| i k)) |T_java.lang.String|)
	//         (isAllocated (|intern:| i k) alloc))))
	vi = builder.registerQuantifiedVariable("i", builder.sortInt);
	vk = builder.registerQuantifiedVariable("k", builder.sortInt);
	ti = builder.buildQVarRef(vi);
	tk = builder.buildQVarRef(vk);
	t0 = builder.buildFnCall(builder.symIntern, new SAny[] { ti, tk });
	t1 = builder.buildFnCall(builder.symTypeOf, new SAny[] { t0 });
	t2 = builder.buildFnCall(builder.symTString, new SAny[] {});
	t3 = builder.buildFnCall(builder.symAlloc, new SAny[] {});
        p0 = builder.buildAnyNE(t0, builder.buildNull());
	p1 = builder.buildAnyEQ(t1, t2);
	p2 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { t0, t3 });
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vi, vk };
	p = builder.buildForAll(vars0, builder.buildAnd(new SPred[] { p0, p1, p2 }), pats, null);
	prover.declareAxiom(p);
	
	//(BG_PUSH
	//  (FORALL (s)
	//    (PATS (|interned:| s))
	//    (is (|interned:| s) |T_boolean|)
	//  ))
	vs = builder.registerQuantifiedVariable("s", builder.sortString);
	ts = builder.buildQVarRef(vs);
	t0 = builder.buildFnCall(builder.symInterned, new SAny[] { ts });
	//p0 = builder.buildPredCall(builder.symInterned, new SAny[] { ts });
	//t0 = builder.buildValueConversion(builder.sortPred, builder.sortBool, (SValue)p0);
	t1 = builder.buildFnCall(builder.symTBoolean, new SAny[] {});
	p1 = builder.buildPredCall(builder.symIs, new SAny[] { t0, t1 });

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vs };
	p = builder.buildForAll(vars0, p1, pats, null);
	prover.declareAxiom(p);

	//(BG_PUSH
	//  (FORALL (i ii k kk)
	//    (PATS (MPAT (|intern:| i k) (|intern:| ii kk)))
	//    (IFF (EQ (|intern:| i k) (|intern:| ii kk))  (EQ i ii)) ))
	vi = builder.registerQuantifiedVariable("i", builder.sortInt);
	vii = builder.registerQuantifiedVariable("ii", builder.sortInt);
	vk = builder.registerQuantifiedVariable("k", builder.sortInt);
	vkk = builder.registerQuantifiedVariable("kk", builder.sortInt);
	ti = builder.buildQVarRef(vi);
	tii = builder.buildQVarRef(vii);
	tk = builder.buildQVarRef(vk);
	tkk = builder.buildQVarRef(vkk);
	t0 = builder.buildFnCall(builder.symIntern, new SAny[] { ti, tk });
	t1 = builder.buildFnCall(builder.symIntern, new SAny[] { tii, tkk });
	p0 = builder.buildIff(builder.buildAnyEQ(t0, t1), builder.buildAnyEQ(ti, tii));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0, t1 };
	vars0 = new QuantVar[] { vi, vii, vk, vkk };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);

	//
	//(BG_PUSH
	//  (FORALL (i k)
	//    (PATS (|intern:| i k))
	//    (|interned:| (|intern:| i k))
	//  ))
	vi = builder.registerQuantifiedVariable("i", builder.sortInt);
	vk = builder.registerQuantifiedVariable("k", builder.sortInt);
	ti = builder.buildQVarRef(vi);
	tk = builder.buildQVarRef(vk);
	t0 = builder.buildFnCall(builder.symIntern, new SAny[] { ti, tk });
	t1 = builder.buildFnCall(builder.symInterned, new SAny[] { t0 });
	p0 = builder.buildIsTrue((SBool)t1);
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vi, vk };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);

	//(BG_PUSH
	//  (FORALL /(x y a)
	//    (PATS (stringCat x y a))
	//    (AND (NEQ (stringCat x y a) null)
	//    	 (NOT (isAllocated (stringCat x y a) a))
	//         (EQ (typeof (stringCat x y a)) |T_java.lang.String|))))
	vx = builder.registerQuantifiedVariable("x", builder.sortString);
	vy = builder.registerQuantifiedVariable("y", builder.sortString);
	va = builder.registerQuantifiedVariable("a", builder.sortTime);
	tx = builder.buildQVarRef(vx);
	ty = builder.buildQVarRef(vy);
	ta = builder.buildQVarRef(va);
	t0 = builder.buildFnCall(builder.symStringCat, new SAny[] { tx, ty, ta });
	t1 = builder.buildFnCall(builder.symTypeOf, new SAny[] { t0 } );
	t2 = builder.buildFnCall(builder.symTString, new SAny[] {} );
        p0 = builder.buildAnyNE(t0, builder.buildNull());
        p1 = builder.buildNot(builder.buildPredCall(builder.symIsAllocated, new SAny[] { t0, ta } ));
        p2 = builder.buildAnyEQ(t1, t2);
	p3 = builder.buildAnd(new SPred[] { p0, p1, p2 } );
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vx, vy, va };
	p = builder.buildForAll(vars0, p3, pats, null);
	prover.declareAxiom(p);

	//(BG_PUSH
	//  (FORALL (x y a b)
	//    (PATS (MPAT (stringCat x y a) (stringCat x y b)))
	//    (IFF (EQ (stringCat x y a) (stringCat x y b)) (EQ a b))))
	vx = builder.registerQuantifiedVariable("x", builder.sortString);
	vy = builder.registerQuantifiedVariable("y", builder.sortString);
	va = builder.registerQuantifiedVariable("a", builder.sortTime);
	vb = builder.registerQuantifiedVariable("b", builder.sortTime);
	tx = builder.buildQVarRef(vx);
	ty = builder.buildQVarRef(vy);
	ta = builder.buildQVarRef(va);
	tb = builder.buildQVarRef(vb);
	t0 = builder.buildFnCall(builder.symStringCat, new SAny[] { tx, ty, ta });
	t1 = builder.buildFnCall(builder.symStringCat, new SAny[] { tx, ty, tb });
	p0 = builder.buildIff(builder.buildAnyEQ(t0, t1), builder.buildAnyEQ(ta, tb));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0, t1 };
	vars0 = new QuantVar[] { vx, vy, va, vb };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);

	// :TODO: typing? what is next anyway?
	//(BG_PUSH
	//  (FORALL (a b i j)
	//    (PATS (MPAT (next a i) (next b j)))
	//	(IFF (EQ (next a i)(next b j))
	//		 (AND (EQ a b)(EQ i j)))))
	//
	//(BG_PUSH
	//  (FORALL (a i) 
	//    (PATS (next a i))
	//    (< a (next a i))))

	//(BG_PUSH
	//  (FORALL (x y xx yy a b)
	//     (PATS (MPAT (stringCat x y a) (stringCat xx yy b)))
	//     (IMPLIES
	//     	  (EQ (stringCat x y a) (stringCat xx yy b))
	//     	  (EQ a b))))
	vx = builder.registerQuantifiedVariable("x", builder.sortString);
	vy = builder.registerQuantifiedVariable("y", builder.sortString);
	vxx = builder.registerQuantifiedVariable("xx", builder.sortString);
	vyy = builder.registerQuantifiedVariable("yy", builder.sortString);
	va = builder.registerQuantifiedVariable("a", builder.sortTime);
	vb = builder.registerQuantifiedVariable("b", builder.sortTime);
	tx = builder.buildQVarRef(vx);
	ty = builder.buildQVarRef(vy);
	txx = builder.buildQVarRef(vxx);
	tyy = builder.buildQVarRef(vyy);
	ta = builder.buildQVarRef(va);
	tb = builder.buildQVarRef(vb);
	t0 = builder.buildFnCall(builder.symStringCat, new SAny[] { tx, ty, ta });
	t1 = builder.buildFnCall(builder.symStringCat, new SAny[] { txx, tyy, tb });
	p0 = builder.buildImplies(builder.buildAnyEQ(t0, t1), builder.buildAnyEQ(ta, tb));
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0, t1 };
	vars0 = new QuantVar[] { vx, vy, vxx, vyy, va, vb };
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);

	//(DEFPRED (stringCatP r x y a0 a1))
	//
	//(BG_PUSH
	//  (FORALL (r x y a0 a1)
	//    (PATS (stringCatP r x y a0 a1))
	//    (IMPLIES (stringCatP r x y a0 a1)
	//    		(AND (NEQ r null)
	//    	 		(isAllocated r a1)
	//    	 		(NOT (isAllocated r a0))
	//    	 		(< a0 a1)
	//         		(EQ (typeof r) |T_java.lang.String|)))))
	vr = builder.registerQuantifiedVariable("r", builder.sortString);
	vx = builder.registerQuantifiedVariable("x", builder.sortString);
	vy = builder.registerQuantifiedVariable("y", builder.sortValue);
	va0 = builder.registerQuantifiedVariable("a0", builder.sortTime);
	va1 = builder.registerQuantifiedVariable("a1", builder.sortTime);
	tr = builder.buildQVarRef(vr);
	tx = builder.buildQVarRef(vx);
	ty = builder.buildQVarRef(vy);
	ta0 = builder.buildQVarRef(va0);
	ta1 = builder.buildQVarRef(va1);
	t0 = builder.buildFnCall(builder.symTypeOf, new SAny[] { tr });
	t1 = builder.buildFnCall(builder.symTString, new SAny[] {});
	p0 = builder.buildPredCall(builder.symStringCatP, new SAny[] { tr, tx, ty, ta0, ta1 });
	p1 = builder.buildAnyNE(tr, builder.buildNull());
        p2 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { tr, ta1 } );
        p3 = builder.buildNot(builder.buildPredCall(builder.symIsAllocated, new SAny[] { tr, ta0 } ));
        p4 = builder.buildIntPred(builder.predLT, (SInt) ta0, (SInt) ta1);
        p5 = builder.buildAnyEQ(t0, t1);
	p6 = builder.buildImplies(p0, builder.buildAnd(new SPred[] { p1, p2, p3, p4, p5 } ));
	pats = new STerm[1][];
	pats[0] = new STerm[] { p0 };
	vars0 = new QuantVar[] { vr, vx, vy, va0, va1 };
	p = builder.buildForAll(vars0, p6, pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPIntegral(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPStrings:");
	// handled by buildArithFunctions in builder

	//; Not in ESCJ8, but should be
	//
	//(BG_PUSH
	//  (FORALL (x y)
	//    (PATS (integralEQ x y))
	//    (IFF
	//      (EQ (integralEQ x y) |@true|)
	//      (EQ x y))))
	//
	//(BG_PUSH
	//  (FORALL (x y)
	//    (PATS (integralGE x y))
	//    (IFF
	//      (EQ (integralGE x y) |@true|)
	//      (>= x y))))
	//
	//(BG_PUSH
	//  (FORALL (x y)
	//    (PATS (integralGT x y))
	//    (IFF
	//      (EQ (integralGT x y) |@true|)
	//      (> x y))))
	//
	//(BG_PUSH
	//  (FORALL (x y)
	//    (PATS (integralLE x y))
	//    (IFF
	//      (EQ (integralLE x y) |@true|)
	//      (<= x y))))
	//
	//(BG_PUSH
	//  (FORALL (x y)
	//    (PATS (integralLT x y))
	//    (IFF
	//      (EQ (integralLT x y) |@true|)
	//      (< x y))))
	//
	//(BG_PUSH
	//  (FORALL (x y)
	//    (PATS (integralNE x y))
	//    (IFF
	//      (EQ (integralNE x y) |@true|)
	//      (NEQ x y))))

	// :TODO: what is this refEQ/refNE good for?
	// we just map it to buildAnyEQ and buildAnyNE in builder
	//(BG_PUSH
	//  (FORALL (x y)
	//    (PATS (refEQ x y))
	//    (IFF
	//      (EQ (refEQ x y) |@true|)
	//      (EQ x y))))
	//
	//(BG_PUSH
	//  (FORALL (x y)
	//    (PATS (refNE x y))
	//    (IFF
	//      (EQ (refNE x y) |@true|)
	//      (NEQ x y))))

    }

    public static void sendBPCondRefl(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPCondRefl:");
	//; === ESCJ 8: Section 5.3

	// reflection handled by casting in Cvc3NodeBuilder
	//
	//(BG_PUSH
	// (FORALL (x y)
	//	 (PATS (termConditional |@true| x y))
	//	 (EQ (termConditional |@true| x y) x)))
	//
	//(BG_PUSH
	// (FORALL (b x y)
	//	 (PATS (termConditional b x y))
	//	 (IMPLIES (NEQ b |@true|)
	//		  (EQ (termConditional b x y) y))))
    }

    public static void sendBPArrayNonNull(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
        if (builder.optNonnullelements) return;

	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPArrayNonNull:");
	//; === Implementation of nonnullelements; not in ESCJ 8 (yet?):
	//
	//(DEFPRED (nonnullelements x e)
	//   (AND (NEQ x null)
	//	(FORALL (i)
	//	   (IMPLIES (AND (<= 0 i)
	//			 (< i (arrayLength x)))
	//		    (NEQ (select (select e x) i) null)))))

	QuantVar vx = builder.registerQuantifiedVariable("x", builder.sortArray);
	QuantVar ve = builder.registerQuantifiedVariable("e", builder.sortElems);
	QuantVar vi = builder.registerQuantifiedVariable("i", builder.sortInt);

	// :TODO:
	// miniscoping i currently makes cvc crash,
	// so had to pull it out
	//QuantVar[] vars0 = new QuantVar[] { vx, ve };
	//QuantVar[] vars1 = new QuantVar[] { vi };
	QuantVar[] vars0 = new QuantVar[] { vx, ve, vi };

	SAny t0 = builder.buildFnCall(builder.symArrayLength, new SAny[] { builder.buildQVarRef(vx) });
	SAny t1 = builder.buildSelect((SMap)builder.buildQVarRef(ve), (SValue)builder.buildQVarRef(vx));
	SAny t2 = builder.buildSelect((SMap)t1, (SInt)builder.buildQVarRef(vi));

	SPred p0 = builder.buildPredCall(builder.symNonNullElems,
					 new SAny[] { builder.buildQVarRef(vx), builder.buildQVarRef(ve) });

	SPred p1 = builder.buildAnyNE(builder.buildQVarRef(vx), builder.buildNull());
	SPred p2 = builder.buildIntPred(builder.predLE, builder.buildInt(0), (SInt)builder.buildQVarRef(vi));
	SPred p3 = builder.buildIntPred(builder.predLT, (SInt)builder.buildQVarRef(vi), (SInt)t0);
	SPred p4 = builder.buildAnyNE(t2, builder.buildNull());
	SPred p5 = builder.buildAnd(p2, p3);
	SPred p6 = builder.buildImplies(p5, p4);
	//SPred p7 = builder.buildForAll(vars1, p6, null, null);
	SPred p7 = p6;

	SPred p8 = builder.buildAnd(p1, p7);
	SPred p9 = builder.buildIff(p0, p8);
	SPred p = builder.buildForAll(vars0, p9, null, null);
	prover.declareAxiom(p);
    }

    public static void sendBPClassLiteral(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPClassLiteral:");

	QuantVar vt = builder.registerQuantifiedVariable("t", builder.sortType);
	QuantVar[] vars0;
	STerm[][] pats;
	SAny t0, t1, t2, t3;
	SPred p, p0, p1, p2;

	//; === Axioms about classLiteral; not in ESCJ 8 (yet?):
	//
	//(BG_PUSH
	// (FORALL (t)
	//	 (PATS (classLiteral t))
	//	 (AND (NEQ (classLiteral t) null)
	//	      (is (classLiteral t) |T_java.lang.Class|)
	//              (isAllocated (classLiteral t) alloc))))
        t0 = builder.buildFnCall(builder.symClassLiteral, new SAny[] { builder.buildQVarRef(vt) });
        t1 = builder.buildFnCall(builder.symTClass, new SAny[] {});
        t2 = builder.buildFnCall(builder.symAlloc, new SAny[] {});
        p0 = builder.buildAnyNE(t0, builder.buildNull());
        p1 = builder.buildPredCall(builder.symIs, new SAny[] { t0, t1 });
        p2 = builder.buildPredCall(builder.symIsAllocated, new SAny[] { t1, t2 });
	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vt };
	p = builder.buildForAll(vars0, builder.buildAnd(new SPred[] {p0, p1, p2}), pats, null);
	prover.declareAxiom(p);
        
	//(BG_PUSH
	// (FORALL (t)
	//	 (PATS (classLiteral t))
	//	 (EQ (classLiteral t) t)
	//))
	t3 = builder.buildValueConversion(builder.sortType, builder.sortRef, (SValue)builder.buildQVarRef(vt));
        p0 = builder.buildAnyEQ(t0, t3);
	p = builder.buildForAll(vars0, p0, pats, null);
	prover.declareAxiom(p);
    }

    public static void sendBPArithMore(Cvc3Prover prover, Cvc3NodeBuilder builder) throws Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3BackgroundPredicate.sendBPArithMore:");

	//:TODO:

	//; === Axioms about properties of integral &, |, and /

	QuantVar vx = builder.registerQuantifiedVariable("x", builder.sortInt);
	QuantVar vy = builder.registerQuantifiedVariable("y", builder.sortInt);
	QuantVar vz = builder.registerQuantifiedVariable("z", builder.sortInt);
	SInt t0, t1, t2, t3;
	SPred p, p0, p1, p2, p3, p4, p5, p6;
	STerm[][] pats;
	QuantVar[] vars0;

	Cvc3Int qvx = (Cvc3Int) builder.wrapExpr(((Cvc3Any)builder.buildQVarRef(vx)).getExpr(), builder.sortInt);
	Cvc3Int qvy = (Cvc3Int) builder.wrapExpr(((Cvc3Any)builder.buildQVarRef(vy)).getExpr(), builder.sortInt);
	Cvc3Int qvz = (Cvc3Int) builder.wrapExpr(((Cvc3Any)builder.buildQVarRef(vz)).getExpr(), builder.sortInt);

	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralAnd x y))
	//  (IMPLIES
	//   (OR (<= 0 x) (<= 0 y))
	//   (<= 0 (integralAnd x y)))))
	//
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralAnd x y))
	//  (IMPLIES
	//   (<= 0 x)
	//   (<= (integralAnd x y) x))))
	//
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralAnd x y))
	//  (IMPLIES
	//   (<= 0 y)
	//   (<= (integralAnd x y) y))))
	//
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralOr x y))
	//  (IMPLIES
	//   (AND (<= 0 x) (<= 0 y))
	//   (AND (<= x (integralOr x y)) (<= y (integralOr x y))))))
	//

	//; ((x >= 0) & (y > 0)) ==> (x/y >= 0 & x >= (x/y) )
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralDiv x y))
	//  (IMPLIES
	//   (AND (<= 0 x) (< 0 y))
	//   (AND (<= 0 (integralDiv x y)) (<= (integralDiv x y) x)))))
	t0 = builder.buildIntFun(builder.funDIV, qvx, qvy);

	p0 = builder.buildIntPred(builder.predLE, builder.buildInt(0), qvx);
	p1 = builder.buildIntPred(builder.predLT, builder.buildInt(0), qvy);
	p2 = builder.buildAnd(p0, p1);

	p3 = builder.buildIntPred(builder.predLE, builder.buildInt(0), t0);
	p4 = builder.buildIntPred(builder.predLE, t0, qvx);
	p5 = builder.buildAnd(p3, p4);

	p6 = builder.buildImplies(p2, p5);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vx, vy };
	p = builder.buildForAll(vars0, p6, pats, null);
	prover.declareAxiom(p);


	//; ((x <= 0) & (y > 0)) ==> (x/y <= 0 & x <= x/y))
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralDiv x y))
	//  (IMPLIES
	//   (AND (<= x 0) (< 0 y))
	//   (AND (<= (integralDiv x y) 0) (<= x (integralDiv x y))))))
	t0 = builder.buildIntFun(builder.funDIV, qvx, qvy);

	p0 = builder.buildIntPred(builder.predLE, builder.buildInt(0), qvx);
	p1 = builder.buildIntPred(builder.predLT, builder.buildInt(0), qvy);
	p2 = builder.buildAnd(p0, p1);
	
	p3 = builder.buildIntPred(builder.predLE, t0, builder.buildInt(0));
	p4 = builder.buildIntPred(builder.predLE, qvx, t0);
	p5 = builder.buildAnd(p3, p4);

	p6 = builder.buildImplies(p2, p5);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vx, vy };
	p = builder.buildForAll(vars0, p6, pats, null);
	prover.declareAxiom(p);


	//; ((x <= z) & (y > 0)) ==> (x/y <= z/y))
	//(BG_PUSH
	// (FORALL (x y z)
	//  (PATS (MPAT (integralDiv z y) (LE x z)))
	//  (IMPLIES
	//   (AND (<= x z) (< 0 y))
	//   (<= (integralDiv x y) (integralDiv z y)))))
	t0 = builder.buildIntFun(builder.funDIV, qvx, qvy);
	t1 = builder.buildIntFun(builder.funDIV, qvz, qvy);

	p0 = builder.buildIntPred(builder.predLE, qvx, qvz);
	p1 = builder.buildIntPred(builder.predLT, builder.buildInt(0), qvy);
	p2 = builder.buildAnd(p0, p1);

	p3 = builder.buildIntPred(builder.predLE, t0, t1);

	p4 = builder.buildImplies(p2, p3);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t1, p0 };
	vars0 = new QuantVar[] { vx, vy, vz };
	p = builder.buildForAll(vars0, p4, pats, null);
	prover.declareAxiom(p);

	//; ( x >= 0 & y < 0) ==> (x/y)<=0
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralDiv x y))
	//  (IMPLIES
	//   (AND (<= 0 x) (< y 0))
	//   (<= (integralDiv x y) 0))))
	t0 = builder.buildIntFun(builder.funDIV, qvx, qvy);

	p0 = builder.buildIntPred(builder.predLE, builder.buildInt(0), qvx);
	p1 = builder.buildIntPred(builder.predLT, qvy, builder.buildInt(0));
	p2 = builder.buildAnd(p0, p1);

	p3 = builder.buildIntPred(builder.predLE, t0, builder.buildInt(0));
	
	p4 = builder.buildImplies(p2, p3);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vx, vy };
	p = builder.buildForAll(vars0, p4, pats, null);
	prover.declareAxiom(p);

	//; ( x <= 0 & y < 0 ) ==> (x/y) >= 0
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralDiv x y))
	//  (IMPLIES
	//   (AND (<= x 0) (< y 0))
	//   (<= 0 (integralDiv x y)))))
	t0 = builder.buildIntFun(builder.funDIV, qvx, qvy);

	p0 = builder.buildIntPred(builder.predLE, qvx, builder.buildInt(0));
	p1 = builder.buildIntPred(builder.predLT, qvy, builder.buildInt(0));
	p2 = builder.buildAnd(p0, p1);

	p3 = builder.buildIntPred(builder.predLE, builder.buildInt(0), t0);
	
	p4 = builder.buildImplies(p2, p3);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vx, vy };
	p = builder.buildForAll(vars0, p4, pats, null);
	prover.declareAxiom(p);

	//; (x <= 0 & y > 0) ==> (x/y) <= 0
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralDiv x y))
	//  (IMPLIES
	//   (AND (<= x 0) (< 0 y))
	//   (<= (integralDiv x y) 0))))
	t0 = builder.buildIntFun(builder.funDIV, qvx, qvy);

	p0 = builder.buildIntPred(builder.predLE, qvx, builder.buildInt(0));
	p1 = builder.buildIntPred(builder.predLT, builder.buildInt(0), qvy);
	p2 = builder.buildAnd(p0, p1);

	p3 = builder.buildIntPred(builder.predLE, t0, builder.buildInt(0));
	
	p4 = builder.buildImplies(p2, p3);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vx, vy };
	p = builder.buildForAll(vars0, p4, pats, null);
	prover.declareAxiom(p);

	//; (x == 0 & y != 0) ==> (x/y)==0
	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralDiv x y))
	//  (IMPLIES
	//   (AND (EQ 0 x) (NOT (EQ 0 y)))
	//   (EQ 0 (integralDiv x y)))))
	t0 = builder.buildIntFun(builder.funDIV, qvx, qvy);

	p0 = builder.buildAnyEQ(builder.buildInt(0), qvx);
	p1 = builder.buildAnyEQ(builder.buildInt(0), qvy);
	p2 = builder.buildAnd(p0, builder.buildNot(p1));

	p3 = builder.buildAnyEQ(builder.buildInt(0), t0);
	
	p4 = builder.buildImplies(p2, p3);

	pats = new STerm[1][];
	pats[0] = new STerm[] { t0 };
	vars0 = new QuantVar[] { vx, vy };
	p = builder.buildForAll(vars0, p4, pats, null);
	prover.declareAxiom(p);

	//(BG_PUSH
	// (FORALL (x y)
	//  (PATS (integralXor x y))
	//  (IMPLIES
	//   (AND (<= 0 x) (<= 0 y))
	//   (<= 0 (integralXor x y)))))
	//
	//(BG_PUSH
	// (FORALL (n)
	//  (PATS (intShiftL 1 n))
	//  (IMPLIES
	//   (AND (<= 0 n) (< n 31))
	//   (<= 1 (intShiftL 1 n)))))
	//
	//(BG_PUSH
	// (FORALL (n)
	//  (PATS (longShiftL 1 n))
	//  (IMPLIES
	//   (AND (<= 0 n) (< n 63))
	//   (<= 1 (longShiftL 1 n)))))
	//

	//; === A few floating point axioms - DRCok
	//;; FIXME - floatingLT etc are predicates here, but are functions in ESC/java - is that a problem?
	//;; FIXME - have to include NaN and infinity

	// LIA ones maked to builder arith functions

	//
	//;; Order axioms
	//(BG_PUSH
	// (FORALL (d dd)
	//  (AND
	//     (OR
	//	(EQ |@true| (floatingLT d dd))
	//	(EQ |@true| (floatingEQ d dd))
	//	(EQ |@true| (floatingGT d dd))
	//     )
	//     (IFF (EQ |@true| (floatingLE d dd)) (OR (EQ |@true| (floatingEQ d dd)) (EQ |@true| (floatingLT d dd))))
	//     (IFF (EQ |@true| (floatingGE d dd)) (OR (EQ |@true| (floatingEQ d dd)) (EQ |@true| (floatingGT d dd))))
	//     (IFF (EQ |@true| (floatingLT d dd)) (EQ |@true| (floatingGT dd d)))
	//     (IFF (EQ |@true| (floatingLE d dd)) (EQ |@true| (floatingGE dd d)))
	//     (NOT (IFF (EQ |@true| (floatingLT d dd)) (EQ |@true| (floatingGE d dd))))
	//     (NOT (IFF (EQ |@true| (floatingGT d dd)) (EQ |@true| (floatingLE d dd))))
	//  )))
	//
	//
	//;; floatingNE
	//(BG_PUSH (FORALL (d dd) (IFF (EQ |@true| (floatingEQ d dd)) (NOT (EQ |@true| (floatingNE d dd)))) ))
	//
	//;; floatADD
	//(BG_PUSH (FORALL (d dd)
	//  (IMPLIES (EQ |@true| (floatingGT d (floatingNEG dd))) (EQ |@true| (floatingGT (floatingADD d dd) |F_0.0|)))
	//))
	//
	//;; floatMUL
	//;;(BG_PUSH (FORALL (d dd) (AND
	//  ;;(IFF (OR (floatingEQ d |F_0.0|) (floatingEQ dd |F_0.0|)) (floatingEQ (floatingMUL d dd) |F_0.0|))
	//  ;;(IMPLIES (AND (floatingGT d |F_0.0|) (floatingGT dd |F_0.0|)) (floatingGT (floatingMUL d dd) |F_0.0|))
	//  ;;(IMPLIES (AND (floatingLT d |F_0.0|) (floatingLT dd |F_0.0|)) (floatingGT (floatingMUL d dd) |F_0.0|))
	//  ;;(IMPLIES (AND (floatingLT d |F_0.0|) (floatingGT dd |F_0.0|)) (floatingLT (floatingMUL d dd) |F_0.0|))
	//  ;;(IMPLIES (AND (floatingGT d |F_0.0|) (floatingLT dd |F_0.0|)) (floatingLT (floatingMUL d dd) |F_0.0|))
	//;;)))
	//
	//;; floatingMOD
	//(BG_PUSH
	// (FORALL (d dd)
	//  (IMPLIES (EQ |@true| (floatingNE dd |F_0.0|)) (AND
	//    (IMPLIES (EQ |@true| (floatingGE d |F_0.0|)) (EQ |@true| (floatingGE (floatingMOD d dd) |F_0.0|)))
	//    (IMPLIES (EQ |@true| (floatingLE d |F_0.0|)) (EQ |@true| (floatingLE (floatingMOD d dd) |F_0.0|)))
	//))))
	//(BG_PUSH (FORALL (d dd) 
	//    (IMPLIES (EQ |@true| (floatingGT dd |F_0.0|)) (AND
	//        (EQ |@true| (floatingGT (floatingMOD d dd) (floatingNEG dd))) 
	//        (EQ |@true| (floatingLT (floatingMOD d dd) dd)) ))
	//))
	//(BG_PUSH (FORALL (d dd) 
	//    (IMPLIES (EQ |@true| (floatingLT dd |F_0.0|)) (EQ |@true| (floatingLT (floatingMOD d dd) (floatingNEG dd)))) ))
	//(BG_PUSH (FORALL (d dd) 
	//    (IMPLIES (EQ |@true| (floatingLT dd |F_0.0|)) (EQ |@true| (floatingGT (floatingMOD d dd) dd))) ))
    }
}
