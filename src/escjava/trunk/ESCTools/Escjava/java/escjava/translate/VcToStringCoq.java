package escjava.translate;

/**
 * Responsible for converting GCExpr to formula Strings for input to Simplify.
 * The GCExpr language is documented elsewhere, as is Simplifys input language.
 */
import java.io.*;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Arrays;
import java.util.Vector;
import java.util.Iterator;
import javafe.ast.*;
import javafe.tc.Types;
import javafe.util.*;
import escjava.ast.*;
import escjava.ast.TagConstants;
import escjava.backpred.BackPred;
import escjava.prover.Atom;


public class VcToStringCoq extends VcToString{

    /* list of already declared variables in the pvs logic 
       like LS, null, Java.lang.Object etc... */
    static public Vector listOfDecl = new Vector();

    /* list of variables of type Types
     * in Coq
     */
    static public Vector listOfTypeAdd = new Vector();
    /* name of the variables that need to be declared
       Before adding a variable to this set, we check if the variable isn't
       already in this set or in listOfDecl */
    static public Vector listOfDeclAdd = new Vector();
    /*
     * list of the variables that are mapped to Z...
     */
    static public Vector listOfIntAdd = new Vector();
    /*
     * list of the variables that are mapped to Bools ...
     */
    static public Vector listOfBoolAdd = new Vector();
    
    /* set containing the name of the new fonctions that need to be declared,
       that are introduced during the creation of gc, but aren't explicitly redeclared
       here normally (because Simplify seems to allow declarations 'on the fly' ??) 

       The second vector contains the number of parameters for functions
       declared in the first one.

       It means :
       listOfDeclFun = < f, g>
       listOfDeclFunNbParam = < 1, 2>

       will be translated to :
       f(a : S) : S
       g(a, b :S) : S
    */
    static public Vector listOfDeclFun = new Vector();
    static public Vector listOfDeclFunNbParam = new Vector();
    
  /**
   * Resets any type-specific information that is accumulated through calls to
   * <code>computeTypeSpecific</code>.
   */
  public static void resetTypeSpecific() {
    integralPrintNames = new Hashtable();
    //+@ set integralPrintNames.keyType = \type(Long);
    //+@ set integralPrintNames.elementType = \type(String);
    // add thresholds
    integralPrintNames.put(minThreshold, String.valueOf(-MaxIntegral));
    integralPrintNames.put(maxThreshold, String.valueOf(MaxIntegral));
  }
  
  /**
   * Prints <code>e</code> as a simple-expression string to <code>to</code>.
   * Any symbolic names created for integral literals in <code>e</code> are
   * added to a static place (variable <code>integralPrintNames</code>) so
   * that successive calls to <code>compute</code> can produce properties
   * about these names.
   */
  public static void computeTypeSpecific(/*@ non_null */Expr e,
                                         /*@ non_null */PrintStream to) {
    VcToStringCoq vts = new VcToStringCoq();//TODO: Find the right way to do this
    vts.printFormula(to, e);
  }
  
  /**
   * Prints <code>e</code> as a verification-condition string to
   * <code>to</code>. Any symbolic names of integral literals stored by the
   * most recent call to <code>computeTypeBackPred</code>, if any, will be
   * considered when producing properties about such symbolic literals.
   */
  public static void compute(/*@  non_null */Expr e,
      /*@  non_null */PrintStream to) {


      Hashtable oldNames = integralPrintNames;
      integralPrintNames = (Hashtable)oldNames.clone();
      listOfDecl.add("ecReturn");
      listOfDecl.add("ecThrow");
      // @review kiniry - Translation of Clement's French comment: 
      // If we are going to do something, always pretty-print!
      //if (escjava.Main.options().prettyPrintVC)
	  
      
      VcToStringCoq vts = new VcToStringCoq();
      vts.printDefpreds(to, vts.getDefpreds(e));
      PrintStream o = null;
//    to.println("\n(EXPLIES(");
      File f = null;
      try {
		f = File.createTempFile("escjava", ".v");
		o = new PrintStream(new FileOutputStream(f));
	} catch (IOException e1) {
		System.out.println("Problem creating/writing the temp file.");
		e1.printStackTrace();
	}
      vts.printFormula(o, e);
      //to.println(" (AND ");
      //to.println(",true))");
      // /* Remove the distinct clause at the end of the output
// 	 it's replaced by declaring pvs variables
//        */
      if(o != null)
    	  o.close();
      to = new PrintStream(new escjava.prover.PPOutputStream(to));
      //vts.distinctSymbols(to);
      vts.stringLiteralAssumptions(to);
      to.print("Load \"defs_unsorted.v\".");
      to.print("(* Start of Coq declarations : *)\n ");
      vts.integralPrintNameOrder(to);

      //to.println("))");
    
      integralPrintNames = oldNames;

      /* This piece of code declares all variables before leaving */
      Iterator i = null;
      String tempString = null; // makes the compiler happy
      Integer tempInteger = null;

      /* list of functions declarations

      It means :
      listOfDeclFun = < f, g>
      listOfDeclFunNbParam = < 1, 2>
      
      will be translated to :
      f(a : S) : S
      g(a, b :S) : S
      
      */
      
      if(listOfDeclFun.size() != listOfDeclFunNbParam.size())
	  System.out.println("Warning, inconsistency in declaration of new functions...");

      if(listOfDeclFun.size()!=0) { /* something to declare */
	  i = listOfDeclFun.iterator();
	  Iterator j = listOfDeclFunNbParam.iterator();	  

	  while(i.hasNext() && j.hasNext()){

	      try {
		  tempString = (String)i.next();
		  tempInteger = (Integer)j.next();
	      }
	      catch(Exception ex){
		  System.out.println("VcToStringCoq::add2Decl *** error *** "+ex);
	      }

	      /* name of the function, for example : g */
	      to.print("Variable " + tempString + ":");
	      char c = 'a';

	      /* declaring (a1, a2 :S) for g for example 
		 note that if there is more than 24 parameters, it will stupidly fail
		 because c++ will come back to a, anyway it should not happen
	      */
	      for( int k = 0; k < tempInteger.intValue(); k++, c++) { 
		  //to.print(c);
		  to.print(" S");
	      
		  if(k < tempInteger.intValue() - 1) /* not the last */
		      to.print(" ->");
		  else /* finishing declaration, adding ) : S at the end */
		      to.print(" -> S.\n"); 
		      //to.print(") : S = "+c +"\n"); // experimental
	      }
	  }

	  to.println();
      }

      /* theorem */
      i = listOfDeclAdd.iterator();

      to.println("Lemma l : \n    forall ");
      printDecl(listOfDeclAdd, "S", to);
      printDecl(listOfTypeAdd, "Types", to);
      printDecl(listOfBoolAdd, "(* bool *) S", to);
      printDecl(listOfIntAdd, "(* Z *) S", to);
      to.print(", \n");
      if(f != null) {
    	  try {
			LineNumberReader lnr = new LineNumberReader(new FileReader(f));
			String line;
			while ((line = lnr.readLine()) != null) {
				to.println(line);
			}
			lnr.close();
		} catch (Exception e1) {
			System.out.println("Problems encountered reading " + f);
			e1.printStackTrace();
		}
          to.print(".\nProof with autosc.");
          to.println("\nstartsc.\n\n");
          to.println("Qed.");
      }

  }
  
  private static void printDecl(Vector list, String strType, PrintStream to) {
	     Iterator i = list.iterator();
	     if(!i.hasNext())
	    	 return;
	      to.print("(");
	      String tempString = "";
	      while(i.hasNext()){
		    
	    	  try{ 
	    		  tempString = (String)i.next();
	    		  if(listOfDeclFun.contains(tempString))
	    			  continue;
	    	
	    	  }
	    	  catch(Exception ex){
	    		  System.out.println("VcToStringCoq::add2Decl *** error *** "+ex);
	    	  }
		
	    	  to.print(tempString);

	    	  if(i.hasNext())
	    		  to.print(" ");
	    	  
	      	}
	      to.print(" : " + strType + ")");
  }
  
  public static void computePC(/*@  non_null */Expr e,
      /*@  non_null */PrintStream to) {
    Hashtable oldNames = integralPrintNames;
    integralPrintNames = (Hashtable)oldNames.clone();
    
    VcToStringCoq vts = new VcToStringCoq();//TODO:Find the right way to do it
    
    to.println("\n(AND ");
    vts.printFormula(to, e);
    vts.distinctSymbols(to);
    vts.stringLiteralAssumptions(to);
    vts.integralPrintNameOrder(to);
    to.println(")");
    
    integralPrintNames = oldNames;
  }
  
  // holds set of symbols used
  //@ spec_public
  protected/*@  non_null */Set symbols = new Set();
  
  // string of initial assumptions
  //@ spec_public
  protected/*@  non_null */Set stringLiterals = new Set();
  
  //+@ invariant integralPrintNames.keyType == \type(Long);
  //+@ invariant integralPrintNames.elementType == \type(String);
  //@ spec_public
  protected static/*@  non_null */Hashtable integralPrintNames;
  
    protected VcToStringCoq() {}
  
  protected String vc2Term(/*@ non_null */Expr e, Hashtable subst) {
    Assert.notNull(e);
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    PrintStream ps = new PrintStream(baos);
    printTerm(ps, subst, e);
    String s = baos.toString();
    ps.close();
    // System.out.println("vc2Term yields: "+s);

    return s;
  }
  
  protected void printDefpreds(/*@  non_null */PrintStream to, DefPredVec preds) {
    for (int i = 0; i < preds.size(); i++) {
      DefPred dp = preds.elementAt(i);
      to.print("(DEFPRED (" + dp.predId);
      for (int j = 0; j < dp.args.size(); j++) {
        to.print(" " + dp.args.elementAt(j).id);
      }
      to.print(") ");
      printFormula(to, dp.body);
      to.print(")\n");
    }
  }
  
  protected DefPredVec preds;
  
  protected DefPredVec getDefpreds(/*@ non_null */Expr e) {
    preds = DefPredVec.make();
    getDefpredsHelper(e);
    return preds;
  }
  
  protected void getDefpredsHelper(/*@ non_null */Expr e) {
    if (e instanceof DefPredLetExpr) {
      DefPredLetExpr dple = (DefPredLetExpr)e;
      preds.append(dple.preds);
    }
    for (int i = 0; i < e.childCount(); i++) {
      Object c = e.childAt(i);
      if (c instanceof Expr) {
        getDefpredsHelper((Expr)c);
      }
    }
  }
  

  
  protected void stringLiteralAssumptions(/*@  non_null */PrintStream to) {
    Enumeration e = stringLiterals.elements();
    while (e.hasMoreElements()) {
      String litname = (String)e.nextElement();
      
      to.print(" ((" + litname + "<> null) /\\");   
      to.print(" ((typeof " + litname + ") == T_java.lang.String))");
      
      // We could also assume "litname" to be allocated (but at this
      // time we don't have the name of the initial value of "alloc";
      // probably it is "alloc", but it would be nice not to have to
      // rely on that here).
    }
  }
  
  // ======================================================================
  
  protected void printFormula(/*@ non_null */PrintStream out,
      /*@ non_null */Expr e) {
    // maps GenericVarDecls to Strings
    // some complex invariant here
    
    Hashtable subst = new Hashtable();
    printFormula(out, subst, e);
  }
  
  protected void printFormula(/*@ non_null */PrintStream out, Hashtable subst,
      /*@ non_null */Expr e) {
    Assert.notNull(e);

    reallyPrintFormula(out, subst, e);

  }


    protected void reallyPrintFormula(/*@ non_null */PrintStream out,
				      Hashtable subst,
				      /*@ non_null */Expr e) {

	//++
// 	System.out.println("VcToStringPvs::reallyPrintFormula");
	//++
    
	switch (e.getTag()) {

	case TagConstants.DEFPREDLETEXPR: {
	    DefPredLetExpr dple = (DefPredLetExpr)e;
	    printFormula(out, subst, dple.body);
	    break;
	}

	case TagConstants.SUBSTEXPR: {
	    SubstExpr se = (SubstExpr)e;
	    // perform current substitution on expression
	    String expr = vc2Term(se.val, subst);
	    // get old val, install new val
	    Object old = subst.put(se.var, expr);
	    //System.out.println("old="+old);
        
	    // print
	    printFormula(out, subst, se.target);
        
	    // restore old state
	    if (old == null) subst.remove(se.var);
	    else subst.put(se.var, old);
        
	    break;
	}
      
	case TagConstants.LABELEXPR: {
	    LabelExpr le = (LabelExpr)e;
	    out.println("((* LBL"+(le.positive ? "POS " : "NEG ")+le.label.toString()+" *) ");
	    printFormula(out, subst, le.expr);
	    out.print(")");
	    break;
	}
	   
	
      
	case TagConstants.GUARDEXPR: {
	    if (!escjava.Main.options().guardedVC) {
		Assert.fail("VcToString.reallyPrintFormula: unreachable");
	    } else {
		GuardExpr ge = (GuardExpr)e;
		String var = escjava.Main.options().guardedVCPrefix
		    + UniqName.locToSuffix(ge.locPragmaDecl);
		//out.print("(IMPLIES |" + var + "| ");
		out.print("(" + replaceBadChar(var) + " -> ");
		printBoolTerm(out, subst, ge.expr);
		out.print(")");
		escjava.Main.options().guardVars.add(var);
		break;
	    }
	}
      

	    //  Operators on formulas
	case TagConstants.BOOLIMPLIES: {
			NaryExpr ne = (NaryExpr)e;
			for (int i = 0; i < ne.exprs.size(); i++) {
				if(i != 0)
					out.print("-> (");
				else
					out.print("(");
				printBoolTerm(out, subst, ne.exprs.elementAt(i));
				out.print(")" );
			}
		}
		break;
	case TagConstants.BOOLAND:
	case TagConstants.BOOLANDX: {
			NaryExpr ne = (NaryExpr)e;
			out.print("(" );
			for (int i = 0; i < ne.exprs.size(); i++) {
				if(i != 0)
					out.print("/\\ (");
				else
					out.print("(");
				printBoolTerm(out, subst, ne.exprs.elementAt(i));
				out.print(")" );
			}
			out.print(")" );
		}
		break;
	case TagConstants.BOOLOR: {
			NaryExpr ne = (NaryExpr)e;
			out.print("(" );
			int count =0;
			for (int i = 0; i < ne.exprs.size(); i++) {
				count ++;
				if(i != 0) {
					Expr ex = ne.exprs.elementAt(i);
					out.print("\\/ (");
					printFormula(out, subst, ex);
					
				}
				else {
					out.print("(");
					printFormula(out, subst, ne.exprs.elementAt(i));
				}
				//out.print(")" );
			}
			for(int i = 0; i <= count; i++ )
				out.print(")" );
		}
		break;
	case TagConstants.BOOLNOT: {
			NaryExpr ne = (NaryExpr)e;
			out.print("(not (");
			printBoolTerm(out, subst, ne.exprs.elementAt(0));
			out.print("))" );
		}
		break;
		
	case TagConstants.ANYEQ:
		out.print("(* Any EQ *)");
		
	case TagConstants.REFEQ:{
		out.print("(* Ref EQ *)");
//		NaryExpr ne = (NaryExpr)e;
//		ExprVec ev = ne.exprs;
//		if(ev.size() > 1){
//			if(isBoolTerm(ev.elementAt(0)) || isBoolTerm(ev.elementAt(1))) {
//				out.print("(");
//    			printBoolTerm(out, subst, ev.elementAt(0));
//	    		out.print(" <-> " );
//    			printBoolTerm(out, subst, ev.elementAt(1));
//    			out.print(")");
//				break;
//			}
//		}
	}
	case TagConstants.TYPEEQ:{
		out.print("(* Type EQ *)");
			NaryExpr ne = (NaryExpr)e;	 
			//special case "the AS trick..."
			ExprVec ev = ne.exprs;
			if(ev.size() > 1){
				switch (ev.elementAt(1).getTag()) {
					case TagConstants.ASFIELD: {
						if(isIntTerm(ev.elementAt(0)))
							out.print("True");
						else {
							// Form of the tree (asfield obj type)
							NaryExpr ex = (NaryExpr)ev.elementAt(1);
							out.print("((* is field *) subtypes (typeof ");
							printTerm(out,subst, ex.exprs.elementAt(0));
							out.print(") ");
							printTerm(out,subst,ex.exprs.elementAt(1));
							out.print(")");
						}
//						out.print("(*as field expr *) True");
						
						break;
					}
						
					case TagConstants.ASLOCKSET: {
						// For now I don't know what to do with a lockset
						out.print("(* AsLockset Expr *) True ");
						break;
					}
					case TagConstants.ASELEMS: {
						// For now I don't know what to do with a lockset
						out.print("(* AsElems Expr *) True ");
						break;
					}
					default:
						if(isIntTerm(ev.elementAt(0)) || isIntTerm(ev.elementAt(1))) {
					    	out.print("(");
					    	int max = ne.exprs.size() - 1;
					    	for (int i = 0; i < max; i++) {
					    		if(i > 0) {
					    			out.print(" /\\ ");
					    		}
					    		out.print("(");
					    		Expr ex1 = ne.exprs.elementAt(i);
					    		Expr ex2 = ne.exprs.elementAt(i + 1);
				    			printIntTerm(out, subst, ex1);
					    		out.print(" = " );
					    		printIntTerm(out, subst, ex2);
				 	    		out.print(")");
					    	}
				 	    	out.print(")");
						}
						else if(isBoolTerm(ev.elementAt(0)) || isBoolTerm(ev.elementAt(1))) {
							out.print("(");
							printBoolTerm(out, subst, ev.elementAt(0));
							out.print(" <-> " );
							printBoolTerm(out, subst, ev.elementAt(1));
							out.print(")");
						}
						else {
				    	/* (EQ a b c d) =>
				    	 * boolAnd(EQ(a ,b), EQ(b,c)) 
				    	 * the following part: boolAnd( EQ(b,c), EQ(c,d)))
				    	 * is _not_ necessary.
				    	 * we HAVE tactics.
				    	 */

				    	out.print("(");
				    	int max = ne.exprs.size() - 1;
				    	for (int i = 0; i < max; i++) {
				    		if(i > 0) {
				    			out.print(" /\\ ");
				    		}
				    		out.print("((");
				    		Expr ex1 = ne.exprs.elementAt(i);
				    		Expr ex2 = ne.exprs.elementAt(i + 1);
				    		out.print("(* " + TagConstants.toString(ex1.getTag()) + "*)");
			    			printTerm(out, subst, ex1);
				    		
				    		out.print(") = (" );
				    		out.print("(* " + TagConstants.toString(ex1.getTag()) + "*)");
				    		printTerm(out, subst, ex2);
				    		
				    		out.print("))");
				    	}
			 	    	out.print(")");
						}
						break;
				}
			}
		}
	 	break;
	case TagConstants.INTEGRALEQ:
	 {
		out.print("(* int eq *)");
	 	NaryExpr ne = (NaryExpr)e;	 
		//special case "the AS trick..."
		ExprVec ev = ne.exprs;
		if(ev.size() > 1){
	    	/* (EQ a b c d) =>
	    	 * boolAnd(EQ(a ,b), EQ(b,c)) 
	    	 * the following part: boolAnd( EQ(b,c), EQ(c,d)))
	    	 * is _not_ necessary.
	    	 * we HAVE tactics.
	    	 */

	    	out.print("(");
	    	int max = ne.exprs.size() - 1;
	    	for (int i = 0; i < max; i++) {
	    		if(i > 0) {
	    			out.print(" /\\ ");
	    		}
	    		out.print("(");
	    		Expr ex1 = ne.exprs.elementAt(i);
	    		Expr ex2 = ne.exprs.elementAt(i + 1);
    			printIntTerm(out, subst, ex1);
	    		out.print(" = " );
	    		printIntTerm(out, subst, ex2);
 	    		out.print(")");
	    	}
 	    	out.print(")");
			break;
		}
	}
 	break;
	case TagConstants.BOOLEQ: {

	 	NaryExpr ne = (NaryExpr)e;	 
	 	out.print("(* Bool eq *)");
		//special case "the AS trick..."
		ExprVec ev = ne.exprs;
		if(ev.size() > 1){
	    	/* (EQ a b c d) =>
	    	 * boolAnd(EQ(a ,b), EQ(b,c)) 
	    	 * the following part: boolAnd( EQ(b,c), EQ(c,d)))
	    	 * is _not_ necessary.
	    	 * we HAVE tactics.
	    	 */

	    	out.print("( "
	    			// + "(* bool eq*)"
	    			);
	    	int max = ne.exprs.size() - 1;
	    	for (int i = 0; i < max; i++) {
	    		if(i > 0) {
	    			out.print(" /\\ ");
	    		}
	    		out.print("(");
	    		Expr ex1 = ne.exprs.elementAt(i);
	    		Expr ex2 = ne.exprs.elementAt(i + 1);
    			printBoolTerm(out, subst, ex1);    			
	    		out.print(" <-> " );
	    		printBoolTerm(out, subst, ex2);    			
	    		out.print(")");	    		
	    	}
 	    	out.print(")");
			break;
		}
	}
 	break;
	case TagConstants.ANYNE:
		out.print("(* ANY neq *)");
	case TagConstants.REFNE:
	case TagConstants.TYPENE:	 
	case TagConstants.INTEGRALNE:
	case TagConstants.BOOLNE: {
	    NaryExpr ne = (NaryExpr)e;
	    out.print("(");
	    printTerm(out, subst, ne.exprs.elementAt(0));
	    out.print(" <> ");
	    printTerm(out, subst, ne.exprs.elementAt(1));
	    out.print(")");
	    break;
	}
      
      


		
	    // PredSyms
	case TagConstants.ALLOCLT:
	case TagConstants.ALLOCLE:
	case TagConstants.LOCKLE:
	case TagConstants.LOCKLT:


	case TagConstants.TYPELE: {
	    NaryExpr ne = (NaryExpr)e;
	    String op;
	    switch (ne.getTag()) {
	    case TagConstants.ALLOCLT:
		op = "lockLT";
		break;
	    case TagConstants.ALLOCLE:
		op = "lockLE";
		break;
	    
	    case TagConstants.LOCKLE:
		op = TagConstants.toVcString(TagConstants.LOCKLE);
		break;
	    case TagConstants.LOCKLT:
		op = TagConstants.toVcString(TagConstants.LOCKLT);
		break;
	    case TagConstants.REFEQ:
		//op = "EQ";
		op = "refEQ";
		break;
	    case TagConstants.REFNE:
		//op = "NEQ";
		op = "refNE";
		break;
	    case TagConstants.TYPELE:
		op = "subtypes";
		//op = "<=";
		break;
	    default:
		Assert.fail("Fall thru");
		op = null; // dummy assignment
	    }
        
	    out.print("(" + op + " ");
	    //out.print(op + "(");
	    for (int i = 0; i < ne.exprs.size(); i++) {
	    	if( i>0 ) out.print(" ");
			//out.print(" ");
			// makes it more 'readable' cough cough...
			printTerm(out, subst, ne.exprs.elementAt(i));
	    }
	    out.print(")");
	    break;
	}
	case TagConstants.BOOLEANLIT:{

	    //++
//	    System.out.println("printTerm::BOOLEANLIT");
	    //++

	    LiteralExpr le = (LiteralExpr)e;
	    if (((Boolean)le.value).booleanValue()) 
	    	out.print("True ");
	    else 
	    	out.print("False ");
	    break;
	}
//	case TagConstants.VARIABLEACCESS: {
//		// if we are called like that we _must_ be a boolean
//		//VariableAccess va = (VariableAccess) e;
//		out.print("(");
//		//if(va.decl.type.getTag() != TagConstants.BOOLEANTYPE)
//		out.print("(S_to_bool ");
//		printTerm(out, subst, e);
//		//if(va.decl.type.getTag() != TagConstants.BOOLEANTYPE)
//		out.print(")");
//		out.print(" = true)");
//		break;
//	}

	default: {
	    if (e.getTag() == TagConstants.DTTFSA) {
		NaryExpr ne = (NaryExpr)e;
		TypeExpr te = (TypeExpr)ne.exprs.elementAt(0);
		if (Types.isBooleanType(te.type)) {
		    // print this DTTFSA as a predicate
		    printDttfsa(out, subst, ne);
		    break;
		}
	    }
	    // not a predicate, must be a term

	    // the two next lines are useless in pvs

	    //out.print("(");
	    printTerm(out, subst, e);
	    //out.print(" = true)");
	    break;
	}
	}
    }

    protected boolean isEven(int i){
	
	int j = i/2;
	
	return ((j * 2) == i);

    }

  // ======================================================================
  
  /**
   * <code>insideNoPats</code> is really a parameter to *
   * <code>printTerm</code>.
   */
  
  protected boolean insideNoPats = false;

    protected void printTerm(/*@ non_null */PrintStream out, Hashtable subst,
			     /*@ non_null */Expr e) {
    
	//++
// 	System.out.println("VcToStringPvs::printTerm");
	//++
    
	int tag = e.getTag();

	switch (tag) {
      
	case TagConstants.SUBSTEXPR: {

	    //++
//	    System.out.println("printTerm::SUBSTEXPR");
	    //++

	    SubstExpr se = (SubstExpr)e;
	    // perform current substitution on expression
	    String expr = vc2Term(se.val, subst);
	    
	    // get old val, install new val
	    Object old = subst.put(se.var, expr);
	    // print
	    printTerm(out, subst, se.target);
        
	    // restore old state
	    if (old == null) subst.remove(se.var);
	    else subst.put(se.var, old);
        
	    break;
	}
      
	case TagConstants.DEFPREDAPPLEXPR: {

	    //++
//	    System.out.println("printTerm::DEFPREDAPPLEXPR");
	    //++


	    DefPredApplExpr dpae = (DefPredApplExpr)e;
	    out.print("(" + dpae.predId);
	    for (int i = 0; i < dpae.args.size(); i++) {
	    	out.print(" ");
	    	printTerm(out, subst, dpae.args.elementAt(i));
	    }
	    out.print(")");
	    break;
	}
      
	case TagConstants.TYPEEXPR: {

	    //++
//	    System.out.println("printTerm::TYPEEXPR");
	    //++

	    TypeExpr te = (TypeExpr)e;
	    
	    //System.out.println(BackPred.simplifyTypeName(te.type));
	    
	    // remove | around type name

	    out.print(replaceBadChar(BackPred.simplifyTypeName(te.type)));
	    break;
	}
      
	    // Literals
      
	    // This handles case 8 of ESCJ 23b:
	case TagConstants.STRINGLIT: {

	    //++
//	    System.out.println("printTerm::STRINGLIT");
	    //++

	    LiteralExpr le = (LiteralExpr)e;
	    String s = "S_" + UniqName.locToSuffix(le.loc);
	    s = Atom.printableVersion(s);
	    stringLiterals.add(s);
	    out.print(s);
	    break;
	}
      
	case TagConstants.BOOLEANLIT: {

	    //++
//	    System.out.println("printTerm::BOOLEANLIT");
	    //++

	    LiteralExpr le = (LiteralExpr)e;
	    if (((Boolean)le.value).booleanValue()) 
	    	out.print("true ");
	    else 
	    	out.print("false ");
	    break;
	}
      
	case TagConstants.CHARLIT:
	case TagConstants.INTLIT: {
	    LiteralExpr le = (LiteralExpr)e;
	    //out.print(integralPrintName(((Integer)le.value).intValue()));

	    /*
	     * In case of special value, this fonction can print
	     * neg2147483648 or pos2147483647 (and normal int like 1 or 2).
	     * But in the latter case, we have to convert it to 
	     * real_to_S(1) otherwise pvs will consider it as a real
	     */

	    String s = integralPrintName(((Integer)le.value).intValue());

	    /* lame way to determine if it's negXXXX or a 'normal int'  */
	    
	    if( s.charAt(0)=='n' || s.charAt(0)=='p' )
		out.print(s);
	    else
		out.print(s);

	    break;
	}
      
	case TagConstants.LONGLIT: {
	    LiteralExpr le = (LiteralExpr)e;
	    out.print(integralPrintName(((Long)le.value).longValue()));
	    break;
	}
      
	case TagConstants.FLOATLIT: {
	    LiteralExpr le = (LiteralExpr)e;
	    out.print("|F_" + ((Float)le.value).floatValue() + "|");
	    break;
	}
      
	case TagConstants.DOUBLELIT: {
	    LiteralExpr le = (LiteralExpr)e;
	    out.print("|F_" + ((Double)le.value).doubleValue() + "|");
	    break;
	}
      
	case TagConstants.NULLLIT:
	    //out.print("null");
	    out.print("null");
	    break;
      
	case TagConstants.SYMBOLLIT: {
	    // Handles case 5 of ESCJ 23b:
	    LiteralExpr le = (LiteralExpr)e;
	    //String s = "|" + (String)le.value + "|";

	    String s = (String)le.value;
	    symbols.add(s);

	    //System.out.println("TagConstants.SYMBOLLIT:"+s);

	    // name of different path to reach end of fonction

	    out.print(replaceBadVarChar(s, PrimitiveType.make(TagConstants.NULLTYPE, 0)));
	    break;
	}
	case TagConstants.FORALL: 
	case TagConstants.EXISTS: {
	    QuantifiedExpr qe = (QuantifiedExpr)e;
	    if (qe.quantifier == TagConstants.FORALL) 
	    	out.print("(forall (");
	    else 
	    	out.print("(exists (");
        
	    String prefix = "";
	    for (int i = 0; i < qe.vars.size(); i++) {
	    	if(i != 0) {
	    		out.print(") (");
	    	}
	    	GenericVarDecl decl = qe.vars.elementAt(i);
	    	Assert.notFalse(!subst.containsKey(decl), "Quantification over "
	    			+ "substituted variable");
	    	out.print(prefix);

	    	// name of the variable
	    	printVarDecl(out, decl);

	    	// type
	    	out.print(" : S");
	    	if(i < qe.vars.size()-1)
	    		out.print(" ");
	    	prefix = " ";
	    }

	    out.print("), ");
	    printFormula(out, subst, qe.expr);
	    out.print(") ");

	    break;
	}	
	
	case TagConstants.VARIABLEACCESS: {

	    //++
//	    System.out.println("VcToStringPvs::printTerm::VariableAccess");
	    //++

	    VariableAccess va = (VariableAccess)e;
	    String to = (String)subst.get(va.decl);

	    /* replace bad char in each case, because
	     * printVarDecl was modified too
	     */
	    
	    if (to != null) 
	    	out.print(replaceBadChar(to));
	    else 
	    	printVarDecl(out, va.decl);
	    break;
	}
    
	case TagConstants.IS: {
    	NaryExpr ne = (NaryExpr)e;
    	
    	out.print("((typeof "); 
    	printTerm(out, subst, ne.exprs.elementAt(0));
    	out.print(") = ");
    	printTerm(out, subst, ne.exprs.elementAt(1));
    	out.print(")");
    	break;
    }
		
    case TagConstants.TYPELE: {
    	NaryExpr ne = (NaryExpr)e;
    	out.print("(subtypes ");
    	out.print(" ");
		printTerm(out, subst, ne.exprs.elementAt(1));
		out.print(")");
    	break;
    }

	case TagConstants.INTEGRALAND:
	case TagConstants.INTEGRALMOD:

	case TagConstants.INTEGRALEQ:
	case TagConstants.INTEGRALNE:

	case TagConstants.INTEGRALSUB:
	case TagConstants.INTEGRALXOR:
    case TagConstants.INTEGRALADD:
	case TagConstants.INTEGRALDIV:
	case TagConstants.INTEGRALGE:
	case TagConstants.INTEGRALGT:
	case TagConstants.INTEGRALLE:
	case TagConstants.INTEGRALLT:
	case TagConstants.INTEGRALMUL:
	case TagConstants.INTEGRALNEG:
	case TagConstants.INTEGRALNOT:
	case TagConstants.INTEGRALOR: {
	    NaryExpr ne = (NaryExpr)e;
	    String op = null; //compiler happy \o/
	    switch (tag) {
	    	case TagConstants.INTEGRALEQ:
	    		op = "integralEQ_bool";
	    		break;
	    	case TagConstants.INTEGRALNE:
	    		op = "integralNE";
	    		break;
	    	case TagConstants.INTEGRALADD:
	    		op = "integralAdd";
		    	break;
		    case TagConstants.INTEGRALMUL:
		    	op = "integralMul";
		    	break;
		    case TagConstants.INTEGRALNEG:
			//op = "- 0";
		    	op = "integralNeg";
		    	break;
		    case TagConstants.INTEGRALSUB:
		    	op = "integralSub";
				break;
		    case TagConstants.INTEGRALGT:
		    	op = "integralGT";
		    	break;
		    case TagConstants.INTEGRALGE:
		    	op = "integralGE";
		    	break;
		    case TagConstants.INTEGRALLT:
			//op = "- 0";
		    	op = "integralLT";
		    	break;
		    case TagConstants.INTEGRALLE:
		    	op = "integralLE";
				break;
			default:
				op = TagConstants.toVcString(tag);
	    }	 
	    out.print("( " + op + " ");
	    //out.print(op + "(");
	    for (int i = 0; i < ne.exprs.size(); i++) {
			/* makes it more readable */
			if(i!=0)
			    out.print(" ");
			
			printIntTerm(out, subst, ne.exprs.elementAt(i));
			
	    }
	    
	    out.print(")");
	    break;
    }

	case TagConstants.SELECT: {
		// The select_int case 
	    NaryExpr ne = (NaryExpr)e;


	    out.print("(select ");
	    for (int i = 0; i < ne.exprs.size(); i++) {
			/* makes it more readable */
			if(i!=0)
			    out.print(" ");
			printSTerm(out, subst, ne.exprs.elementAt(i));
	    }
	    out.print(")");
		break;
	}
	case TagConstants.STORE: {
		// The store_int case 
	    NaryExpr ne = (NaryExpr)e;
	    String arr = "";
	    if(isIntegralTag(ne.exprs.elementAt(1).getTag()))
    		arr = "arr_";
	    if(isIntegralTag(ne.exprs.elementAt(2).getTag()))
	    		out.print("("+ arr +"store_int ");
	    else if(isBooleanTag(ne.exprs.elementAt(2).getTag())) {
	    		out.print("("+ arr + "store_bool ");
	    }
	    else
	    	out.print("("+arr+"store ");
	    for (int i = 0; i < ne.exprs.size(); i++) {
			/* makes it more readable */
			if(i!=0)
			    out.print(" ");
			
			printTerm(out, subst, ne.exprs.elementAt(i));
	    }
	    out.print(")");
		break;
	}
	case TagConstants.BOOLNOT: {
	    NaryExpr ne = (NaryExpr)e;
	    out.print("(not ");
	    //out.print(op + "(");
	    for (int i = 0; i < ne.exprs.size(); i++) {
			/* makes it more readable */
			if(i!=0)
			    out.print(" ");			
			printBoolTerm(out, subst, ne.exprs.elementAt(i));
			
	    }
	    
	    out.print(")");
	    break;
    }
	
	case TagConstants.ANYNE:
		//out.print("(* ANY neq *)");
	case TagConstants.REFNE:
	case TagConstants.TYPENE: {
	    NaryExpr ne = (NaryExpr)e;
	    out.print("(");
	    printTerm(out, subst, ne.exprs.elementAt(0));
	    out.print(" <> ");
	    printTerm(out, subst, ne.exprs.elementAt(1));
	    out.print(")");
	    break;
	}
	case TagConstants.METHODCALL: {
		NaryExpr ne = (NaryExpr)e;
	    String op = null; //compiler happy \o/

			
			/*
			 * Here you catch the call to function like
			 * java.lang.Throwable#_state
			 */
	
		op = ne.methodName.toString();
		op = replaceBadChar(op);
	
			//++
	//		System.out.println("printTerm::METHODCALL "+op);
			//++
		out.print("(" + op);
		Expr exp = ne.exprs.elementAt(0);
		if(exp.getTag() == TagConstants.DTTFSA) {
			NaryExpr nn = (NaryExpr) exp;
			for (int i = 3; i < nn.exprs.size(); i++) {
		        out.print(" ");
		        Expr ei = nn.exprs.elementAt(i);
		        printSTerm(out, subst, ei);
			}
			add2DeclFun(op,nn.exprs.size() - 3);
		}
		else {
			for (int i = 0; i < ne.exprs.size(); i++) {
		        out.print(" ");
		        Expr ei = ne.exprs.elementAt(i);
		        printSTerm(out, subst, ei);
			}
			add2DeclFun(op,ne.exprs.size());
		}
		out.print(")");
		/* in order to declare the fonction after */
		
		break;
	}
	case TagConstants.BOOLAND:
	case TagConstants.BOOLANDX:
	case TagConstants.BOOLOR: {
	    NaryExpr ne = (NaryExpr)e;
	    String op = null;
	    switch(tag) {
	    	case TagConstants.BOOLOR:
	    		op = " \\/ ";
	    		break;

	    	case TagConstants.BOOLANDX:
	    	case TagConstants.BOOLAND:
	    		op = " /\\ ";
	    		break;
	    	default:
	    		op = null;
	    		break;
	    }
	    out.print("(");
	    printBoolTerm(out, subst, ne.exprs.elementAt(0));
	    out.print(op);
	    printBoolTerm(out, subst, ne.exprs.elementAt(1));
	    out.print(")");
	    break;
	}

	case TagConstants.ARRAYFRESH:
	case TagConstants.ARRAYLENGTH:{
	    NaryExpr ne = (NaryExpr)e;
	    String op = TagConstants.toVcString(tag);

	    // (typeof X) => typeOf( )

	    out.print("( " + op + " ");
	    //out.print(op + "(");
	    for (int i = 0; i < ne.exprs.size(); i++) {

		/* makes it more readable */
		if(i!=0)
		    out.print(" ");
			printSTerm(out, subst, ne.exprs.elementAt(i));
	    }
	    out.print(")");
	    break;
	    
	}
    case TagConstants.ALLOCLT:
	case TagConstants.ALLOCLE:
	case TagConstants.ARRAYMAKE:
	case TagConstants.ARRAYSHAPEMORE:
	case TagConstants.ARRAYSHAPEONE:
	case TagConstants.ASELEMS:
	case TagConstants.ASFIELD:
	case TagConstants.ASLOCKSET:
	
	case TagConstants.BOOLIMPLIES:
	case TagConstants.BOOLNE:
	case TagConstants.CLASSLITERALFUNC:
	case TagConstants.CONDITIONAL:
	case TagConstants.ELEMSNONNULL:
	case TagConstants.ELEMTYPE:
	case TagConstants.ECLOSEDTIME:
	case TagConstants.FCLOSEDTIME:
        
	case TagConstants.FLOATINGADD:
	case TagConstants.FLOATINGDIV:
	case TagConstants.FLOATINGEQ:
	case TagConstants.FLOATINGGE:
	case TagConstants.FLOATINGGT:
	case TagConstants.FLOATINGLE:
	case TagConstants.FLOATINGLT:
	case TagConstants.FLOATINGMOD:
	case TagConstants.FLOATINGMUL:
	case TagConstants.FLOATINGNE:
	case TagConstants.FLOATINGNEG:
	case TagConstants.FLOATINGSUB:
        

		
	case TagConstants.INTSHIFTL:
	case TagConstants.LONGSHIFTL:
	case TagConstants.INTSHIFTR:
	case TagConstants.LONGSHIFTR:
	case TagConstants.INTSHIFTRU:
	case TagConstants.LONGSHIFTRU:

		
		
	case TagConstants.INTERN:
	case TagConstants.INTERNED:
	case TagConstants.BOOLEQ: 
	case TagConstants.ISALLOCATED:
	case TagConstants.ISNEWARRAY:
	case TagConstants.LOCKLE:
	case TagConstants.LOCKLT:
	case TagConstants.MAX:

	case TagConstants.REFEQ:

	case TagConstants.STRINGCAT:
	case TagConstants.STRINGCATP:
	case TagConstants.TYPEEQ:
	case TagConstants.TYPEOF:
	case TagConstants.UNSET:
	case TagConstants.VALLOCTIME: {
	    NaryExpr ne = (NaryExpr)e;
	    String op = TagConstants.toVcString(tag);

	    // (typeof X) => typeOf( )

	    out.print("( " + op + " ");
	    //out.print(op + "(");
	    for (int i = 0; i < ne.exprs.size(); i++) {

		/* makes it more readable */
		if(i!=0)
		    out.print(" ");
			printTerm(out, subst, ne.exprs.elementAt(i));
	    }
	    out.print(")");
	    break;
	    
	}

	case TagConstants.CAST: {

	    //++
//	    System.out.println("TagConstants.CAST");
	    //++

	    NaryExpr ne = (NaryExpr)e;
	    Assert.notFalse(ne.exprs.size() == 2);
	    Expr x = ne.exprs.elementAt(0);
	    TypeExpr t = (TypeExpr)ne.exprs.elementAt(1);
        
	    if (Types.isBooleanType(t.type)) {
		// Peephole optimization to remove casts to boolean, since
		// anything is a boolean in the underlying logic (it either
		// equals |@true| or it doesn't). The reason this peephole
		// optimization is performed here, rather than in trExpr
		// and trSpecExpr, is that then any expression cast to a
		// boolean will be printed as a term, not as a predicate.
		// This may sometimes be useful for boolean DTTFSA expression,
		// which are printed as predicate whenever they occur in
		// predicate positions.
	    	out.print("(* boolean *)");
	    	printTerm(out, subst, x);
	    } else {
		out.print("(");
		out.print(TagConstants.toVcString(tag));
		out.print(" ");
		printTerm(out, subst, x);
		out.print(" ");
		printTerm(out, subst, t);
		out.print(")");
	    }
	    break;
	}
      
	case TagConstants.DTTFSA: {
	    NaryExpr ne = (NaryExpr)e;
	   // out.print("(* dttfsa*)");
	    printDttfsa(out, subst, ne);
	    break;
	}
      
	default:
	    Assert.fail("Bad tag in GCTerm: " + "(tag=" + tag + ","
			+ TagConstants.toVcString(tag) + ") " + e);
	}
    }

  //@ requires ne.op == TagConstants.DTTFSA;
  protected void printDttfsa(/*@ non_null */PrintStream out, Hashtable subst,
      /*@ non_null */NaryExpr ne) {
    LiteralExpr lit = (LiteralExpr)ne.exprs.elementAt(1);
    String op = (String)lit.value;
    if (ne.exprs.size() == 2) {
      out.print(op);
    } else if (op.equals("identity")) {
      Assert.notFalse(ne.exprs.size() == 3);
      Expr e2 = ne.exprs.elementAt(2);
      printTerm(out, subst, e2);
    } else {
      //out.print("((* DTTFSA *)");
      out.print(op);
      for (int i = 2; i < ne.exprs.size(); i++) {
        out.print(" ");
        Expr ei = ne.exprs.elementAt(i);
        printTerm(out, subst, ei);
      }
      out.print(")");
    }
  }

  
  // ======================================================================
  
  protected void printVarDecl(/*@ non_null */PrintStream out, GenericVarDecl decl) {
      // remove bacChar 

      //out.print(Atom.printableVersion(UniqName.variable(decl)));
	  Type t = decl.type;
	  
	  //out.print("(*  "+TagConstants.toString(t.getTag()) + t + "*)");
	 
      out.print(replaceBadVarChar(Atom.printableVersion(UniqName.variable(decl)), t));
  }
  
  // ======================================================================
  
  protected static final long MaxIntegral = 1000000;
  
  protected static final/*@ non_null */Long minThreshold = new Long(-MaxIntegral);
  
  protected static final/*@ non_null */Long maxThreshold = new Long(MaxIntegral);
  
  /**
   * * Convert an integral # into its printname according to the rules * of ESCJ
   * 23b, part 9.
   */
  
  protected/*@ non_null */String integralPrintName(long n) {
    if (-MaxIntegral <= n && n <= MaxIntegral) {
      return String.valueOf(n);
    }
    
    Long l = new Long(n);
    String name = (String)integralPrintNames.get(l);
    if (name != null) {
      return name;
    }
    
    if (n == -n) {
      // Need to handle minlong specially...
      name = "neg" + String.valueOf(n).substring(1);
    } else if (n < 0) {
      name = "neg" + String.valueOf(-n);
    } else {
      name = "pos" + String.valueOf(n);
    }
    
    integralPrintNames.put(l, name);
    return name;
  }
  
  /** Generates the inequalities that compare the integral literals
   * that were replaced in <code>integralPrintName</code> by symbolic
   * names.
   **/
  
  protected void integralPrintNameOrder(/*@ non_null */PrintStream ps) {
    int n = integralPrintNames.size();
    Assert.notFalse(2 <= n); // should contain the two thresholds
    if (n == 0) {
      return;
    }
    
    Long[] keys = new Long[n];
    Enumeration e = integralPrintNames.keys();
    for (int i = 0; e.hasMoreElements(); i++) {
      Long l = (Long)e.nextElement();
      keys[i] = l;
    }
    Arrays.sort(keys);
    
    /* added for pvs */
    StringBuffer pvsDecl = new StringBuffer("\n");
    StringBuffer pvsAxiom = new StringBuffer("\n");
    boolean somethingToDeclare = false;

    String valueI = (String)integralPrintNames.get(keys[0]);

    /* loop invariant:  valueI == integralPrintNames.get(keys[i]); */
    for (int i = 0; i < n - 1; i++) {

	/* This loop can be runned even if their is no declaration
	   That's the need for somethingToDeclare raises */
		
      String valueNext = (String)integralPrintNames.get(keys[i + 1]);
      if (keys[i] == minThreshold) {
        Assert.notFalse(keys[i + 1] == maxThreshold);
      } else {

	  // Ugly hack to print it only the first time
	  if(!somethingToDeclare) {
	      pvsAxiom.append("integralAxiom : AXIOM(");
	      somethingToDeclare = true;
	  }

	  /* lame way to determine if it's negXXXX or 10000 
	     (as we must declare only negXXXX in this case) */

	  pvsAxiom.append("(");

	  if( valueI.charAt(0)=='n' || valueI.charAt(0)=='p' )
	      /* valueI is the int declared */
	      pvsDecl.append(valueI+ " : S");
	  else 
	      pvsDecl.append(valueNext+ " : S");

	  pvsAxiom.append(valueI + " < "+ valueNext);
	  
	  pvsDecl.append("\n");
	  pvsAxiom.append(")");

      }

      if( i < n - 2 && i != 0) /* another declaration after */
	  pvsAxiom.append("AND");

      valueI = valueNext;
    }

    if(somethingToDeclare)
	pvsAxiom.append(")");

    ps.print(pvsDecl.toString());
    ps.print(pvsAxiom.toString());
    
  }
  
  static {
    resetTypeSpecific();
  }

static private int add2VarDecl(String s, Type t){
	
	if( s.charAt(0) == '%')
	    return 0;

	if(listOfDecl.contains(s))
		return 0;

	if(listOfDeclAdd.contains(s))
		return 0;
	if(listOfTypeAdd.contains(s))
		return 0;
	if(listOfIntAdd.contains(s))
		return 0;
	if(listOfBoolAdd.contains(s))
		return 0;
	switch (t.getTag()) {
		case TagConstants.INTTYPE:
			listOfIntAdd.add(s);
			break;
		case TagConstants.BOOLEANTYPE:
			listOfBoolAdd.add(s);
			break;
		default:
			listOfDeclAdd.add(s);
	}
	
	//++
//	System.out.println("Adding "+s+" to the listOfDecl");
	//++

	return 1;
    }
static private int add2Decl(String s){
	
	if( s.charAt(0) == '%')
	    return 0;

	if(listOfDecl.contains(s))
		return 0;
	if(listOfTypeAdd.contains(s))
		return 0;
	listOfTypeAdd.add(s);	
	
	//++
//	System.out.println("Adding "+s+" to the listOfDecl");
	//++

	return 1;
    }

    static private int add2DeclFun(String s, int nbParameters){
    	if( s.charAt(0) == '%')
    		return 0;
    	if(listOfDeclFun.contains(s))
    		return 0;

    	listOfDeclFun.add(s);

    	/* this is so crappy, not to be able to push an int direclty */
    	listOfDeclFunNbParam.add(new Integer(nbParameters));

	//++
//	if(listOfDeclFun.size() != listOfDeclFunNbParam.size())
//	    System.out.println("Warning, inconsistency in declaration of new functions...");
	//++

	//++
//	System.out.println("Adding "+s+", with arity "+nbParameters+" to listOfDeclFun");
	//++

	return 1;
    }

    public static String replaceBadChar(String s){
    	s = replaceBadChar_intern(s);
    	add2Decl(s);
    	return s;
    }
    private static String replaceBadChar_intern(String s) {
//    	 remove beginning and ending |
    	if(s.charAt(0) == '|')
    	    s = s.substring(1,s.length()-1);

    	if(s.charAt(s.length()-1) == '|')
    	    s = s.substring(0,s.length()-2);

    	s = s.replace('@','_').replace('#','_').replace('|','_').replace('.','_').replace(':','_').replace('<','_').replace('>','_').replace('-','_').replace('^','_').replace(',','_').replace('[','_').replace(']','_').replace('!','_').replace('(','_').replace(')','_').replace(' ','_');

    	if(s.compareTo("o") == 0) /* handle the case where a variable
    				     is named just 'o' which is a special
    				     variable in pvs */
    	    s = "o_";

    	/* delete _ at the beginning of variable names, coz it's forbidden in pvs */
    	while(s.charAt(0)=='_')
    	    s = s.substring(1,s.length());
	
    	return s;
    }
    public static String replaceBadVarChar(String s, Type t){
    	s = replaceBadChar_intern(s);
    	add2VarDecl(s, t);
    	return s;
    }
    
    public boolean isIntegralTag(int tag) {
    	return (tag == TagConstants.INTEGRALADD) || (tag == TagConstants.INTEGRALDIV)
    		|| (tag == TagConstants.INTEGRALSUB) || (tag == TagConstants.INTEGRALMUL) 
    		|| (tag == TagConstants.INTEGRALNEG) || (tag == TagConstants.INTLIT)|| (tag == TagConstants.CHARLIT);
    }
    public boolean isBooleanTag(int tag) {
    	return !(isIntegralTag(tag) || tag == TagConstants.VARIABLEACCESS 
    			|| tag == TagConstants.SELECT || tag == TagConstants.STORE 
    			|| tag == TagConstants.ARRAYLENGTH
    			|| tag == TagConstants.SYMBOLLIT || tag == TagConstants.NULLLIT
    			|| tag == TagConstants.METHODCALL || tag == TagConstants.DEFPREDAPPLEXPR);
   }
    private boolean isBoolTerm(Expr e) {
  	  int tag = e.getTag();
//  	  if(tag == TagConstants.VARIABLEACCESS) {
//  			VariableAccess va = (VariableAccess)e;
//  			Type t = va.decl.type;
//  			if(t.getTag() == TagConstants.BOOLEANTYPE)
//  				return true;
//  		} else 
  			return (isBooleanTag(tag)) ;
//  	  return false;
    }
    private boolean isIntTerm(Expr e) {
    	int tag = e.getTag();
//  	  if(tag == TagConstants.VARIABLEACCESS) {
//  			VariableAccess va = (VariableAccess)e;
//  			Type t = va.decl.type;
//  			if(t.getTag() == TagConstants.INTTYPE)
//  				return true;
//  		} else 
    	return (isIntegralTag(tag)) ;
//  	  return false;
    }
    private  void printBoolTerm(PrintStream out, Hashtable subst,Expr e ) {
  	  out.print("(");
  	  if(!isBoolTerm(e)) {
  		  out.print("S_to_bool (");
  	  }	
  	  printFormula(out, subst, e);
 	  if(!isBoolTerm(e)) {
  		  out.print(") = true");
  	  }	
  	  out.print(")");
    }
    private  void printIntTerm(PrintStream out, Hashtable subst,Expr e ) {
    	  out.print("(");
      	  if(!isIntTerm(e)) {
      		  out.print("S_to_Z (");
      	  }	
      	  printTerm(out, subst, e);
     	  if(!isIntTerm(e)) {
      		  out.print(")");
      	  }	
      	  out.print(")");
    }
    
    private  void printSTerm(PrintStream out, Hashtable subst,Expr e ) {
  	  out.print("(");
    	  if(isIntTerm(e)) {
    		  out.print("Z_to_S (");
    	  }	
    	  printTerm(out, subst, e);
   	  if(isIntTerm(e)) {
    		  out.print(")");
   	  }	
      out.print(")");
  }
}
