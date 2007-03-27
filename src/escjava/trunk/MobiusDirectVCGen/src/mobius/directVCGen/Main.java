package mobius.directVCGen;

import java.util.Enumeration;
import java.util.Vector;

import javafe.ast.DelegatingPrettyPrint;
import javafe.ast.Expr;
import javafe.ast.FieldDecl;
import javafe.ast.GenericVarDecl;
import javafe.ast.Identifier;
import javafe.ast.MethodDecl;
import javafe.ast.PrettyPrint;
import javafe.ast.RoutineDecl;
import javafe.ast.StandardPrettyPrint;
import javafe.ast.TypeDecl;
import javafe.ast.TypeDeclElem;
import javafe.ast.VariableAccess;
import javafe.tc.OutsideEnv;
import javafe.tc.TypeSig;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.FatalError;
import javafe.util.Info;
import javafe.util.Location;
import javafe.util.Set;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.vcgen.VCGenVisitor;
import escjava.Options;
import escjava.ast.ConditionVec;
import escjava.ast.EscPrettyPrint;
import escjava.ast.GuardedCmd;
import escjava.ast.Spec;
import escjava.ast.TagConstants;
import escjava.backpred.FindContributors;
import escjava.pa.Traverse;
import escjava.tc.TypeCheck;
import escjava.translate.GC;
import escjava.translate.GetSpec;
import escjava.translate.Helper;
import escjava.translate.InitialState;
import escjava.translate.InlineConstructor;
import escjava.translate.LabelInfoToString;
import escjava.translate.NoWarn;
import escjava.translate.Targets;
import escjava.translate.TrAnExpr;
import escjava.translate.Translate;
import escjava.translate.UniqName;
import escjava.translate.VcToString;

public class Main extends escjava.Main {
	public static void main(/*@ non_null @*/ String[] args) {
		int exitcode = compile(args);
		if (exitcode != 0) 
			System.exit(exitcode);
	}
	
	
	public static int compile(String[] args) {
	    try {
	    	Main t = new Main();
	    	//instance = t;
	        int result = t.run(args);
	        return result;
	    } catch (OutOfMemoryError oom) {
	        Runtime rt = Runtime.getRuntime();
	        long memUsedBytes = rt.totalMemory() - rt.freeMemory();
	        System.out.println("java.lang.OutOfMemoryError (" + memUsedBytes +
			       " bytes used)");
	        //oom.printStackTrace(System.out);
	        return outOfMemoryExitCode;
	    }
	}
	
	
	/*
	 * Remove the check for the use of a legitimate VM
	 * (non-Javadoc)
	 * @see escjava.Main#preload()
	 */
	public void preload() {
	    	OutsideEnv.setListener(this);
	}
	
	/**
	 * This method is called by SrcTool on the TypeDecl of each
	 * outside type that SrcTool is to process.
	 *
	 * <p> In addition, it calls itself recursively to handle types
	 * nested within outside types.
	 */
	//@ also
	//@ requires td != null;
	public void handleTD(TypeDecl td) {
	    long startTime = currentTime();
	    javafe.tc.TypeSig sig = TypeCheck.inst.getSig(td);
	
	    if (!options().quiet)
	        System.out.println("\n" + sig.toString() + " ...");
	
	    if (Location.toLineNumber(td.getEndLoc()) < options().startLine)
	        return;
	
	    // Do actual work:
	    boolean aborted = processTD(td);
	
	    if (!options().quiet)
	        System.out.println("  [" + timeUsed(startTime)
	                           + " total]"
	                           + (aborted ? " (aborted)" : "") );
	
	    /*
	     * Handled any nested types:  [1.1]
	     */
	    TypeDecl decl = sig.getTypeDecl();
	    for (int i=0; i<decl.elems.size(); i++) {
	        if (decl.elems.elementAt(i) instanceof TypeDecl)
	        	handleTD((TypeDecl)decl.elems.elementAt(i));
	    }
	}
	
	
	/**
	 * Run all the requested stages on a given TypeDecl; return true
	 * if we had to abort.
	 *
	 */
	//@ requires td != null;
	//@ requires (* td is not from a binary file. *);
	@SuppressWarnings("unchecked")
	public boolean processTD(TypeDecl td) {
		long startTime = currentTime();
		int errorCount = ErrorSet.errors;
		TypeSig sig = TypeCheck.inst.getSig(td);
		/* FindContributors scope = */ new FindContributors(sig);
	    
	    processTD_stage1(td, sig, errorCount);
	    System.out.println(currentTime() - startTime);
	    Vector<IFormula> vcs= new Vector<IFormula>();
	    vcs = (Vector<IFormula>) td.accept(new VCGenVisitor(), vcs);
	    //sig.accept(new VCGenVisitor(), vcs);
	    System.out.println(vcs);
//	    FindContributors scope =  new FindContributors(sig);
//	    if (stages < 2) {
//			return false;
//	    }
//	    
//	    processTD_stage2(td, sig, scope);
//	    if ( stages < 3) {
//	    	return false;
//	    }
//	    
//	    InitialState initState = processTD_stage3(td, sig, scope, startTime);
//	    
//	    TypeDeclElem[] tdes = td.elems.toArray();
//	    for (TypeDeclElem tde: tdes) {
//			if (((options().inlineConstructors && 
//					!Modifiers.isAbstract(td.modifiers))
//			    // only process inlined versions of methods
//			  && (!InlineConstructor.isConstructorInlinable(tde) ||
//					    InlineConstructor.isConstructorInlinedMethod((MethodDecl) tde)))	     
//			|| (!options().inlineConstructors || 
//						Modifiers.isAbstract(td.modifiers))) {
//				
//				processTD_stage4to5(initState, tde, sig);
//			}
//	    }
	    return false;
	    
	}
	
	/**
	 * Stage 1: Do Java type checking then print Java types if we've been
	 * asked to.
	 */
	public boolean processTD_stage1(TypeDecl td, TypeSig sig, int errorCount) {
	
	    NoWarn.typecheckRegisteredNowarns();
	
		// Create a pretty-printer that shows types
		DelegatingPrettyPrint p = new javafe.tc.TypePrint();
		p.setDel(new EscPrettyPrint(p, new StandardPrettyPrint(p)));
		System.out.println("\n**** Source code with types:");
		p.print(System.out, 0, td);
	
	    // Turn off extended static checking and abort if any errors
	    // occured while type checking *this* TypeDecl:
	    if (errorCount < ErrorSet.errors) {
			if (stages>1) {
			    stages = 1;
			    ErrorSet.caution("Turning off extended static checking " + 
	                                     "due to type error(s)");
			}
			return false;
	    }
	    
	    
		return true;
	}
	
	/**
	 * Stage 2: Generate the type-specific background predicate
	 */
	public boolean processTD_stage2(TypeDecl td, TypeSig sig, FindContributors scope) {
		int errorCount;
	
	    // Generate the type-specific background predicate
	    errorCount = ErrorSet.errors;
	    if (Info.on) Info.out("[ Finding contributors for " + sig + "]");
	    
	    VcToString.resetTypeSpecific();
	
	    if (Info.on) Info.out("[ Found contributors for " + sig + "]");
	
	
	    // Turn off extended static checking and abort if any type errors
	    // occured while generating the type-specific background predicate:
	    if (errorCount < ErrorSet.errors) {
		stages = 1;
		ErrorSet.caution("Turning off extended static checking " + 
				 "due to type error(s)");
		return false;
	    }
	
	    if (options().testRef) makePrettyPrint().print(System.out,0,td);
		return true;
	}
	
	
	/**
	 * Stage 3: Generate guarded commands, and print them
	 */
	public InitialState processTD_stage3(TypeDecl td, TypeSig sig, FindContributors scope, long startTime) {
		LabelInfoToString.reset();
		InitialState initState = new InitialState(scope);
		LabelInfoToString.mark();
	
		if (!options().quiet)
		    System.out.println("    [" + timeUsed(startTime) + "]");
		return initState;
	
	}
	
	
	
	/**
	 * Stages 3+..6 as requested on a TypeDeclElem.
	 *
	 * requires te is not from a binary file, sig is the
	 * TypeSig for te's parent, and initState != null.
	 */
	//@ requires sig != null && initState != null;
	public void processTD_stage4to5(InitialState initState, TypeDeclElem te,
				     TypeSig sig) {
	    // Only handle methods and constructors here:
	    if (!(te instanceof RoutineDecl))
	        return;
	    RoutineDecl r = (RoutineDecl)te;
	
	
	    long startTime = java.lang.System.currentTimeMillis();
	    if (!options().quiet) {
	        String name = TypeCheck.inst.getRoutineName(r) +
	            javafe.tc.TypeCheck.getSignature(r);
	        System.out.println("\n" + sig.toString() + ": " +
			       name + " ...");
	    }
	
	    // Do the actual work, handling not implemented exceptions:
	    String status = "error";
	
	    ///////////////////////////////////////////////////////
	    ///     Remove one of this RoutineDecl 's           ///
	    ///     annotations and continue,                   ///
	    ///     each time returning results                 ///
	    ///     (and annotation removed)        ##Incomplete///
	    ///////////////////////////////////////////////////////
	   
//	    if (options().consistencyCheck){
//	    	
//	    	Consistency c = new Consistency();
//	    	c.consistency(r,sig,initState,startTime);
//	    }
//	    else {
	    
      try {
        status = processRoutineDecl(r, sig, initState);
      } catch (javafe.util.NotImplementedException e) {
    	  // continue - problem already reported
    	  status = "not-implemented";
      } catch (FatalError e) {
    	  // continue;
      }
      if (!options().quiet)
    	  System.out.println("    [" + timeUsed(startTime) + "]  "
    			  + status);

    }
	
	
	
	
	
	
	public String processRoutineDecl(/*@ non_null */ RoutineDecl r,
	      /*@ non_null */ TypeSig sig,
	      /*@ non_null */ InitialState initState) {
		if (r.body == null && !Main.options().idc) 
			return "passed immediately";
		if (r.parent.specOnly && !Main.options().idc) 
			return "passed immediately";
		if ( Location.toLineNumber(r.getEndLoc()) < options().startLine )
			return "skipped";
		String simpleName = TypeCheck.inst.getRoutineName(r).intern();
	    String fullName = sig.toString() + "." + simpleName +
	    	javafe.tc.TypeCheck.getSignature(r);
	    fullName = removeSpaces(fullName).intern();
	    if (options().routinesToSkip != null &&
	    		(options().routinesToSkip.contains(simpleName) ||
	    				options().routinesToSkip.contains(fullName))) {
	            return "skipped";
		}
	    if (options().routinesToCheck != null &&
	    		!options().routinesToCheck.contains(simpleName) &&
	    		!options().routinesToCheck.contains(fullName)) {
	    	return "skipped";
	    }
	    
	    processRoutine_stage3gc(r, initState);
	
		
		// ==== Start stage 4 ====
		if (stages<4)
		    return "ok";
			
		// ==== Start stage 5 ====
		// Skipping stage 5
		
		return "great";
	}
	
	
	
	
	private void processRoutine_stage3gc(RoutineDecl r, InitialState initState) {
	// ==== Stage 3 continues here ====
	/*
	 * Translate body into a GC:
	 */	        
	// don't check the body if we're checking some other inlining depth
		Translate.globallyTurnOffChecks(gctranslator.inlineCheckDepth > 0);
	
		LabelInfoToString.resetToMark();
		GuardedCmd gc = computeBody(r, initState);
			    
		UniqName.resetUnique();
	
		if (gc==null)
		    return;
	   
		System.out.println("\n**** Guarded Command:");
		((EscPrettyPrint)PrettyPrint.inst).print(System.out, 0, gc);
		System.out.println("");
	}
	   
	public static String removeSpaces(/*@ non_null */ String s) {
        while (true) {
            int k = s.indexOf(' ');
			if (k == -1) {
			    return s;
			}
			s = s.substring(0, k) + s.substring(k+1);
        }
    }
	
	
	/**
	 * This method computes the guarded command (including assuming
	 * the precondition, the translated body, the checked
	 * postcondition, and the modifies constraints) for the method or
	 * constructor <code>r</code> in scope <code>scope</code>.
	 *
	 * @return <code>null</code> if <code>r</code> doesn't have a body.
	 */
	
	//@ requires r != null;
	//@ requires initState != null;
	protected Vector<IFormula> computeVCs(RoutineDecl r, InitialState initState) {
		if (r.getTag() == TagConstants.METHODDECL &&
				((MethodDecl)r).body == null && !Main.options().idc) {
			// no body
			return null;
		}

		// don't check the routine if it's a helper
		if (Helper.isHelper(r)) {
			return null;
		}
		
		FindContributors scope = new FindContributors(r);
		TrAnExpr.initForRoutine();
		/*
		 * Compute an upper bound for synTargs if -O7 given.
		 *
		 * For now, do this via the kludge of calling trBody...  !!!!
		 */
		Set predictedSynTargs = null;
		if (!options().useAllInvPreBody) {
			long T = java.lang.System.currentTimeMillis();
			/*
			 * Compute translation assuming synTargs is empty:
			 * (gives same set of targets faster than using null)
			 */
			GuardedCmd tmpBody;
			if (r.body==null && Main.options().idc) {
				tmpBody=null;
				predictedSynTargs=new Set();
			}
			else {
				tmpBody=gctranslator.trBody(r, scope,
						initState.getPreMap(),
						/*predictedSynTargs*/new Set(),
						null,
						/* issueCautions */ false);
				if (options().noDirectTargetsOpt)
					predictedSynTargs = Targets.normal(tmpBody);
				else
					predictedSynTargs = Targets.direct(tmpBody);
			}
			if (options().statsTime)
				System.out.println("      [prediction time: " + timeUsed(T) + "]");
		   	}
		
		
		
		   /*
		* Translate the body:
		*/
		/* Note: initState.preMap is the same for all declarations.
		   This may be overkill (FIXME).
		   It might be better to use information from scope directly
		   since it is generated from the routine decl.
		   However, I don't know for sure what would go missing.  DRCok
		*/
		GuardedCmd body;
		Set fullSynTargs;
		   Set synTargs;
		// Denotes whether the method has body or not
		// used in GetSpec.surroundBodyBySpec()
		boolean nobody=false;
		if (r.body==null && Main.options().idc)
		{
		  GuardedCmd gc3=GC.gets(GC.ecvar, GC.ec_return);
		  nobody=true;
		  //GuardedCmd gc2=GC.assume(GC.falselit);
		  //GuardedCmd gc3=GC.seq(gc1,gc2);
		  body=gc3;
		  if (r.getTag()==TagConstants.CONSTRUCTORDECL)
		  {
		    // get java.lang.Object
		TypeSig obj = escjava.tc.Types.javaLangObject();
		FieldDecl owner = null; // make the compiler happy
		boolean found = true;
		boolean save = escjava.tc.FlowInsensitiveChecks.inAnnotation;
		try {
		  escjava.tc.FlowInsensitiveChecks.inAnnotation = true;
		  owner = escjava.tc.Types.lookupField(obj, 
					Identifier.intern("owner"), 
					obj);
		} catch (javafe.tc.LookupException e) {
		  found = false;
		} finally {
		  escjava.tc.FlowInsensitiveChecks.inAnnotation = save;
		}
		// if we couldn't find the owner ghost field, there's nothing to do
		    if (found) 
		    {
		      VariableAccess ownerVA = TrAnExpr.makeVarAccess(owner,
								      Location.NULL);
		      Expr ownerNull = GC.nary(TagConstants.REFEQ, 
					       GC.select(ownerVA,GC.resultvar), 
					       GC.nulllit);
		      GuardedCmd gcOwner=GC.assume(ownerNull);
		      body=GC.seq(gc3,gcOwner);
		    }
		  }
		  fullSynTargs=new Set();
		  synTargs=new Set();
		}
		else
		{
		
		  body = gctranslator.trBody(r, scope,
					     initState.getPreMap(),
					     predictedSynTargs, null,
					     /* issueCautions */ true);
		  fullSynTargs=Targets.normal(body);
		  if (options().noDirectTargetsOpt)
		       synTargs = fullSynTargs;
		  else
		       synTargs = Targets.direct(body);
		
		}
		
		/*
		 * Verify predictedSynTargs if present that
		 * synTargs is a subset of predictedSynTargs.
		 */
		if (predictedSynTargs != null) {
			Enumeration e = synTargs.elements();
			while (e.hasMoreElements()) {
				GenericVarDecl target = (GenericVarDecl)(e.nextElement());
				Assert.notFalse(predictedSynTargs.contains(target));
			}
		}
		
		TrAnExpr.translate = gctranslator;
		Spec spec = GetSpec.getSpecForBody(r, scope, synTargs,
				initState.getPreMap());
		GetSpec.addAxioms(Translate.axsToAdd,spec.preAssumptions);
		gctranslator.addMoreLocations(spec.postconditionLocations);
		
		// if the current RoutineDecl corresponds to one of our
		// constructor-inlined methods, then zero out its postconditions
		if (r instanceof MethodDecl &&
				InlineConstructor.isConstructorInlinedMethod((MethodDecl) r))
		    	spec.post = ConditionVec.make();
		GuardedCmd fullCmd = 
			GetSpec.surroundBodyBySpec(body, spec, scope, fullSynTargs,
					initState.getPreMap(),
					r.getEndLoc(),nobody);
			
		// loop invariant guessing, based on assertions inside a loop
		/*
		   if (Main.options().loopTranslation == Options.LOOP_SAFE) {
		      LoopInvariantGuessing.traverse(fullCmd, gctranslator);
		   }
		 */
		   
		if (Main.options().loopTranslation == Options.LOOP_SAFE &&
		       Main.options().predAbstract) {
			long T = java.lang.System.currentTimeMillis();
			Traverse.compute(fullCmd, initState, gctranslator);
			if (options().statsTime) {
				System.out.println("      [predicate abstraction time: " + 
						timeUsed(T) + "]");
			}
		}
		Translate.addTraceLabelSequenceNumbers(fullCmd);
			
		return new Vector<IFormula>();	
	}
}
