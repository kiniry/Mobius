/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.pa;

import java.util.Hashtable;
import java.util.Enumeration;
import java.util.Vector;
import java.io.*;

import javafe.ast.*;
import javafe.util.Set;
import javafe.util.Location;
import javafe.util.Assert;
import javafe.util.StackVector;
import javafe.tc.Types;

import escjava.*;
import escjava.ast.*;
import escjava.ast.TagConstants;
import escjava.translate.*;
import escjava.sp.SPVC;
import escjava.sp.*;
import escjava.prover.*;
import escjava.pa.generic.*;

import mocha.wrappers.jbdd.*;

public class PredicateAbstraction {

    public static ASTDecoration paDecoration = new ASTDecoration("paDecoration");
    
    static GuardedCmd abstractLoop(LoopCmd g, GuardedCmd context, Set env) {
	PredicateAbstraction pa = (PredicateAbstraction) paDecoration.get(g);	
	if (pa == null) {
	    pa = new PredicateAbstraction(g, env);
	    paDecoration.set(g, pa);
	}
	return pa.abstractLoopHelper(context, env);
    }

    private static boolean quantifyAssumptions = !Boolean.getBoolean("PAnoQuantifyAssumptions");
    ExprVec invariants = ExprVec.make();
    private jbddManager bddManager;
    public Abstractor abstractor;
    private LocalVarDeclVec skolemConstants;
    private ExprVec loopPredicates;
    private GuardedCmd body;
    private GuardedCmd bodyDesugared = GC.fail();
    private GuardedCmd havoc;
    private int startLoc;
    public int nQueries=0;
    long milliSecsUsed;
    GCProver perfCount;
    
    private final StackVector code = new StackVector();
    private final GenericVarDeclVec temporaries = GenericVarDeclVec.make();

    PredicateAbstraction(LoopCmd g, Set env) {

	body = GC.seq(g.guard, g.body);
	startLoc = g.getStartLoc();

	Set vds = Targets.normal(body);

	if( Main.inferPredicates ) {
	    //System.out.println("Before inf: "+g.predicates);
	    inferPredicates(g, env, vds);
	    //System.out.println("After inf: "+g.predicates);
	}
	
	this.skolemConstants = g.skolemConstants;
	this.loopPredicates = g.predicates;
	this.bddManager = new jbddManager( loopPredicates.size() );

	if( System.getProperty("PABDT") != null ) {
	    this.abstractor = new BinaryDecisionTreeAbstractor(bddManager);
	} else if( System.getProperty("PA3n") != null ) {
	    this.abstractor = new EnumClausesAbstractor(bddManager);
	} else if( System.getProperty("PANK") != null ) {
	    this.abstractor = new EnumNFindK(bddManager,
					     Integer.parseInt(System.getProperty("PANK")));
	} else {
	    this.abstractor = new EnumMaxClausesFindMinAbstractor(bddManager);
	}

	code.push();

	Translate translate = (new Translate());
	GuardedCmd modifyGc = translate.modify(vds, g.locStart);

	if( Main.preciseTargets ) {
	    Set aTargets = ATarget.compute( VarInCmd.make(g.tempVars, g ));
	    modifyGc = translate.modifyATargets( aTargets, g.getStartLoc());
	}

	code.addElement(modifyGc);

	for (Enumeration e = vds.elements(); e.hasMoreElements();) {
	    GenericVarDecl vd = (GenericVarDecl)e.nextElement();
	    
	    if (!vd.id.toString().endsWith("@init")) {
		code.addElement(GC.assume(TrAnExpr.targetTypeCorrect(vd, g.oldmap)));
	    }
	}
	
	for (int i = 0; i < g.invariants.size(); i++) {
	    Condition cond = g.invariants.elementAt(i);
	    code.addElement(GC.assume(cond.pred));
	}

	havoc = GC.seq(GuardedCmdVec.popFromStackVector(code));
    }

    private GuardedCmd abstractLoopHelper(GuardedCmd context, Set env) {
	int step = 0;
	milliSecsUsed -= java.lang.System.currentTimeMillis();

	code.push();
	for(int j=0; j<skolemConstants.size();j++) {
	    LocalVarDecl sc = skolemConstants.elementAt(j);
	    code.addElement(GC.assume(TrAnExpr.typeAndNonNullCorrectAs(sc, sc.type, null, true, null)));
	}
	context = GC.seq( context, 
			  GC.seq( GuardedCmdVec.popFromStackVector(code)));


	System.out.println("Step " + step + ": Computing for loop at "
			   +Location.toString( startLoc )
			   +" num preds = "+loopPredicates.size()
			   + "....");

	perfCount = new GCProver(bddManager, loopPredicates, GC.skip(), null);
	
	GCProver p = new GCProver(bddManager, loopPredicates, context, null);
	boolean atfixpoint = abstractor.union(p);
	p.done();
	perfCount.addPerfCounters(p);

	System.out.println("  reachable size: "+p.size(abstractor.get()));
	
	while (!atfixpoint) {
	    ExprVec invs = p.concretize(abstractor.getClauses());

	    if( quantifyAssumptions ) {
		invs = skolemQuantInvariants(skolemConstants, invs,
					     Location.NULL, Location.NULL);
	    }

	    System.out.println("Step " + ++step + ": Computing....");
	    GuardedCmd c = GC.seq( context, havoc, 
				   GC.assume(GC.and(invs)));
	    // from shaz
	    // c = GC.seq( context, havoc, GC.assume(e) );
	    milliSecsUsed += java.lang.System.currentTimeMillis();
	    bodyDesugared = Traverse.computeHelper(body, c, env);	
	    milliSecsUsed -= java.lang.System.currentTimeMillis();

	    if( Main.pgc ) {
		System.out.println("\n**** Guarded Command c:");
		((EscPrettyPrint)PrettyPrint.inst).print(System.out, 0, c);
		System.out.println("");
		System.out.println("\n**** Guarded Command body:");
		((EscPrettyPrint)PrettyPrint.inst).print(System.out, 0, body);
		System.out.println("");
		System.out.println("\n**** Guarded Command bodyDesugared:");
		((EscPrettyPrint)PrettyPrint.inst).print(System.out, 0, bodyDesugared);
		System.out.println("");
	    }
	    p = new GCProver(bddManager, loopPredicates, GC.seq(c, bodyDesugared), p);
	    atfixpoint = abstractor.union(p);
	    p.done();
	    perfCount.addPerfCounters(p);

	    System.out.println("  reachable size: "+p.size(abstractor.get()));
	}

	invariants = skolemQuantInvariants(skolemConstants,
					   p.concretize(abstractor.getClauses()),
					   Location.NULL,
					   Location.NULL);

	milliSecsUsed += java.lang.System.currentTimeMillis();
	System.out.println("Finished loop at "
			   +Location.toString( startLoc ) );
	return VarInCmd.make(temporaries, 
			     GC.seq(havoc, 
				    GC.assume(GC.and(invariants)),
				    bodyDesugared,
				    GC.fail()));
    }

    public static ExprVec skolemQuantInvariants(LocalVarDeclVec skolemConstants,
						ExprVec invs,
						int sloc, int eloc) {
				  
	// Now, assume the inferred invariants at the beginning of the loop,
	// universally quantified by the skolem constants
	    
	ExprVec r = ExprVec.make();

	for(int i=0; i<invs.size(); i++) {
	    Expr inv = invs.elementAt(i);
	    
	    GenericVarDeclVec decls = GenericVarDeclVec.make();
	    ExprVec ttc = ExprVec.make();
	    for(int j=0; j<skolemConstants.size();j++) {
		LocalVarDecl sc = skolemConstants.elementAt(j);
		if( mentions( inv, sc ) ) {
		    decls.addElement(sc);
		    ttc.addElement( TrAnExpr.typeAndNonNullCorrectAs(sc, sc.type, null, true, null) );
		}
	    }

	    Expr f = GC.quantifiedExpr( sloc, eloc,
					TagConstants.FORALL,
					decls,
					GC.implies( GC.and( ttc ),
						    inv ),
					    null );
	    r.addElement( f );
	}
	
	return r;
    }

    private static boolean mentions(Expr e, GenericVarDecl d) {
	if( e instanceof VariableAccess ) {
	    return ((VariableAccess)e).decl == d;
	} else {
	    for(int i=0; i<e.childCount(); i++) {
		Object c = e.childAt(i);
		if( c instanceof Expr && mentions((Expr)c,d) ) {
		    return true;
		}
	    }
	    return false;
	}
    }

    private void inferPredicatesOld(LoopCmd g, Set env, Set targets) {
	Set t = new Set(targets.elements());
	t.intersect(env);

	for (Enumeration e = t.elements(); e.hasMoreElements();) {
	    GenericVarDecl vd = (GenericVarDecl)e.nextElement();
	    if( vd.type != null ) {
		if( escjava.tc.Types.isIntegralType( vd.type ) ) {
		    // guess vd >= 0
		    ExprVec vec = ExprVec.make();
		    int loc = g.getStartLoc();
		    vec.addElement( VariableAccess.make(vd.id, loc, vd) );
		    vec.addElement( LiteralExpr.make( TagConstants.INTLIT,
								   new Integer(0),
								   loc ));
		    
		    Expr pred = NaryExpr.make( loc, loc, TagConstants.INTEGRALGE, vec );
		    g.predicates.addElement( pred );
		}

		if ( escjava.tc.Types.isReferenceType( vd.type ) ) {
		    // guess vd != null
		    ExprVec vec = ExprVec.make();
		    int loc = g.getStartLoc();
		    vec.addElement( VariableAccess.make(vd.id, loc, vd) );
		    vec.addElement( LiteralExpr.make( TagConstants.NULLLIT,
								   null,
								   loc ));
		    
		    Expr pred = NaryExpr.make( loc, loc, TagConstants.REFNE, vec );
		    g.predicates.addElement( pred );		    
		}
	    }
	}
    }


    private void inferPredicates(LoopCmd g, Set env, Set targets) {

	int loc = g.getStartLoc();

	LocalVarDecl sc = LocalVarDecl.make(Modifiers.NONE, null, Identifier.intern("sc"),
					    Types.intType, loc, null, loc);

	boolean useSC = false;
	ExprVec boundsSC = ExprVec.make();
	VariableAccess sca = VariableAccess.make(sc.id, loc, sc);

	//System.out.println("Getting targets for : "+g);
	Set t = ATarget.compute(g); 
	//System.out.println("Targets: "+t);
	

	// predicates based on environment
      outerLoop:
	for (Enumeration e = env.elements(); e.hasMoreElements();) {
	    GenericVarDecl vd = (GenericVarDecl)e.nextElement();
	    if( vd.id.toString().indexOf('@') != -1 ) {
		// not a user var
		continue;
	    }
	    for (Enumeration e2 = t.elements(); e2.hasMoreElements();) {
		ATarget at = (ATarget)e2.nextElement();
		if( at.x == vd ) {
		    // a target; will deal with below
		    continue outerLoop;
		}
	    }
	    if( vd.type != null ) {
		if( escjava.tc.Types.isIntegralType( vd.type ) ) {
		    // guess sc < vd
		    boundsSC.addElement( GC.nary( loc, loc, TagConstants.INTEGRALLT,
						  sca,
						  VariableAccess.make(vd.id, loc, vd)));
		}
	    }
	}

	for (Enumeration e = t.elements(); e.hasMoreElements();) {
	    ATarget at = (ATarget)e.nextElement();
	    VariableAccess va = VariableAccess.make( at.x.id, Location.NULL, at.x );
	    Expr vaOld = (Expr)g.oldmap.get(at.x);
	    
	    switch( at.indices.length ) {
	      case 0:
		{
		    if( at.x.type != null ) {
			guessPredicate( va, vaOld, at.x.type, g.predicates, loc, sca, boundsSC);
		    }
		}
		break;

	      case 1:
		{
		    if( at.x instanceof FieldDecl && at.x.type != null && at.indices[0] != null ) {
			guessPredicate( GC.select( va, at.indices[0]),
					GC.select( vaOld, at.indices[0]),
					at.x.type, g.predicates, loc, sca, boundsSC);
		    }
		}
		break;

	      case 2:
		{ // elems[..][..]
		    if( at.indices[0] != null ) {
			Type type = null;
			switch( at.indices[0].getTag() ) {
			    case TagConstants.VARIABLEACCESS:
				{
				    GenericVarDecl vd = ((VariableAccess)at.indices[0]).decl;
				    if( vd.type != null ) {
					Assert.notFalse( vd.type instanceof ArrayType );
					type = ((ArrayType)vd.type).elemType;
				    }
				}
				break;

			  case TagConstants.SELECT:
			      {
				  NaryExpr ne = (NaryExpr)at.indices[0];
				  Expr arg0 = ne.exprs.elementAt(0);
				  if( arg0 instanceof VariableAccess ) {
				      GenericVarDecl vd = ((VariableAccess)arg0).decl;
				      if( vd.type != null ) {
					  Assert.notFalse( vd.type instanceof ArrayType );
					  type = ((ArrayType)vd.type).elemType;
				      }
				  }
			      }
			      break;
			}

			if( type != null ) {
			    Expr index;
			    if(at.indices[1] == null ) {
				index = sca;
				useSC = true;
			    } else {
				index = at.indices[1];
			    }
			    guessPredicate( GC.select( GC.select( va, at.indices[0]), index),
					    null,
					    type, g.predicates, loc, sca, boundsSC);
			}
		    }
		}
		break;
	    }
	}

	if( useSC ) {
	    	g.skolemConstants.addElement(sc);
		// guess sc >= 0
		g.predicates.addElement( GC.nary( loc, loc, TagConstants.INTEGRALGE, sca,
						  LiteralExpr.make(TagConstants.INTLIT, new Integer(0),
								   loc) ) );
		g.predicates.append(boundsSC);
	}
    }

    private void guessPredicate( Expr e, Expr eOld, Type type, ExprVec predicates, int loc, Expr sca, ExprVec boundsSC ) {

	if( type != null ) {
	    Expr pred;
	    
	    if( Types.isIntegralType( type ) ) {
		if( eOld != null) {
		    // guess e >= eOld and e <= eOld
		    
		    pred = GC.nary( loc, loc, TagConstants.INTEGRALGE, e, eOld );
		    predicates.addElement( pred );
		    pred = GC.nary( loc, loc, TagConstants.INTEGRALLE, e, eOld );
		    predicates.addElement( pred );
		} else {
		    // guess e >= 0
		    pred = GC.nary( loc, loc, TagConstants.INTEGRALGE, e,
				    LiteralExpr.make( TagConstants.INTLIT,
								   new Integer(0),
								   loc ));
		    predicates.addElement( pred );
		}
		// guess sc < e
		pred = GC.nary( loc, loc, TagConstants.INTEGRALLT, sca, e );
		boundsSC.addElement( pred );
	    }
	    
	    if ( Types.isReferenceType( type ) ) {
		// guess e != null
		pred = GC.nary( loc, loc, TagConstants.REFNE, e,
				LiteralExpr.make( TagConstants.NULLLIT,
						  null, loc ) );
		predicates.addElement( pred ); 
	    }
	}
    }
		
    /*
    private void computeMentionsSet(ASTNode n, Set s) {
	if( n instanceof VariableAccess ) {
	    VariableAccess va = (VariableAccess)n;
	    if( n.decl != null ) {
		s.add(n.decl);
	    }
	}
	for(int i=0; i<n.childCount(); i++) {
	    Object c = n.childAt(i);
	    computeMentionsSet(c,s);
	}
    }
    */
	
}
