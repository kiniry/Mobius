package mobius.directVCGen.bico;

import java.util.LinkedList;
import java.util.List;

import mobius.bico.bicolano.coq.CoqStream;
import mobius.bico.executors.ABasicExecutor;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directvcgen.vcgen.struct.Post;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * The Executor to generate the method formalisation with the annotations.
 * 
 * @see mobius.bico.executors.MethodExecutor
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationMethodExecutor extends ABasicExecutor {
  /** precondition name. */
  private static final String namePre = "pre";
  /** postcondition name. */
  private static final String namePost = "post";
  /** assertion list name. */
  private static final String nameAssertion = "assertion";
  /** assumption list name. */
  private static final String nameAssumption = "assumption";
  /** specification name. */
  private static final String nameSpec = "spec";
  
  
  /** the current method (routine) that is treated - bcel style. */
  private final MethodGen fMeth;
  
  /** the stream where to write the annotations. */
  private final CoqStream fAnnotOut;
  

  
  /**
   * Creates a method executor.
   * @param be the parent executor
   * @param annotationOut the stream to write the annotations to
   * @param clzz the class that is being treated
   * @param met the method that is being treated
   */
  public AnnotationMethodExecutor(final ABasicExecutor be, 
                                  final CoqStream annotationOut, 
                                  final ClassGen clzz, 
                                  final Method met) {
    super(be);
    
    if (met == null) {
      throw new NullPointerException();
    }
    fMeth = new MethodGen(met, clzz.getClassName(), clzz.getConstantPool());
    fAnnotOut = annotationOut;
  }

  /** {@inheritDoc}  */
  @Override
  public void start() {
    Lookup.getInst().computePreconditionArgs(fMeth);
    doMethodPreAndPostDefinition();
  }
  
  private void doMethodPreAndPostDefinition() {
    final String nameModule = getMethodHandler().getName(fMeth);

    int needed = 0;
    if (fMeth.getInstructionList() != null) {
      needed = fMeth.getInstructionList().getEnd().getPosition(); 
    }
    final String defaultSpecs = "(" + needed + "%nat,,global_spec)";

    final CoqStream out = getAnnotationOut();
    out.startModule(nameModule);
    
    // pre and post def
    doMethodPre();
    doMethodPost();
    out.definition("global_spec", "GlobalMethSpec", 
                   "(" + namePre + " ,, " + namePost + ")");
    out.println();
    
    // assertion and assumption def
    final String [] annots =  AnnotationCollector.getAssertion(out, fMeth); 
    if (annots == null) {
      System.out.println(fMeth + " was not annotated!");
    }
    out.definition(nameAssertion, annots[0]);
    out.definition(nameAssumption, annots[1]);
    out.definition("local_spec", "LocMethSpec",
                   "(" + nameAssertion + " ,, " + nameAssumption + ")");
    out.println();
    
    // al together
    out.definitionStart(nameSpec);
    out.incPrintln();
    out.println("(" + defaultSpecs + ",,local_spec). ");
    out.decTab();
    out.endModule(nameModule);
    out.println();    
  }
  
  /**
   * Returns the output stream to write the annotation file.
   * @return an outputstream
   */
  protected CoqStream getAnnotationOut() {
    return fAnnotOut;
  }
  
  

  /**
   * Prints the method precondition. Generates 2 definitions,
   * one mk_namePre, being the one to use with the source memory model
   * the other namePre, to use with the bytecode memory model. 
   * 
   */
  private void doMethodPre() {
    final CoqStream out = getAnnotationOut();

    final List<QuantVariableRef> list = Lookup.getInst().getPreconditionArgs(fMeth);

    String varsAndType = "";

    for (Term qvr: list) {
      final String vname = Formula.generateFormulas(qvr).toString();
      varsAndType += " (" + vname + ": " + Formula.generateType(qvr.getSort()) +  ")";
      
    }
    
    out.definitionStart("mk_" + namePre);
    out.incPrintln();
    out.println("fun " + varsAndType + " => ");
    out.incTab();
    out.println(Formula.generateFormulas(Lookup.getInst().getPrecondition(fMeth)) + ".");
    out.decTab();
    out.decTab();
    
    out.definitionStart(namePre + " (s0:InitState)", "list Prop");
    out.incPrintln();
    final String vars = doLetPre();
    out.incTab();
    //out.println(tab, "   let " + Ref.varThis + " := (do_lvget (fst s0) 0%N)" + " in " +
    out.println("(mk_" + namePre +  " " + vars + "):: nil.");
    out.decTab();
    out.decTab();
  }
  
  /**
   * Prints the method postcondition. Generates 2 definitions,
   * one mk_namePost, being the one to use with the source memory model
   * the other namePost, to use with the bytecode memory model. 
   */
  private void doMethodPost() {
    final CoqStream out = getAnnotationOut();
    // definition of the mk method
    out.println("Definition mk_" + namePost + " := ");
    final List<QuantVariableRef> list = Lookup.getInst().getPreconditionArgsWithoutHeap(fMeth);
    
    String varsAndType = "";
    
    
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    varsAndType += "(" + olhname + ": " + Formula.generateType(Heap.varPre.getSort()) +  ")";
    
    
    
    final String hname = Formula.generateFormulas(Heap.var).toString();
    varsAndType += "(" + hname + ": " + Formula.generateType(Heap.var.getSort()) +  ")";
    
    
    for (Term qvr: list) {
      final String vname = Formula.generateFormulas(qvr).toString();

      varsAndType += " (" + vname + ": " + Formula.generateType(qvr.getSort()) +  ")";
      
    }
        
    Post normalPost = Lookup.getInst().getNormalPostcondition(fMeth);
    final QuantVariableRef varRes = normalPost.getRVar();
    if (varRes != null) {
      final QuantVariableRef v = normalPost.getRVar();
      final Term f = Heap.valueToSort(v, varRes.getSort());
      //System.out.println(f);
      normalPost = new Post(v, normalPost.nonSafeSubst(v, f));
    }
    Post excpPost = Lookup.getInst().getExceptionalPostcondition(fMeth);
    out.incTab();
    out.println("fun " + "(t: ReturnVal) " + varsAndType + " => ");
    out.incTab();
    out.println("match t with");
    final boolean hasRet = !(fMeth.getReturnType().equals(Type.VOID));
    
    if (hasRet) {
      out.println("| Normal (Some " + 
                                       Formula.generateFormulas(normalPost.getRVar()) + 
                                       ") =>");
    }
    else {
      out.println("| Normal None =>");
    }
    
    // momentary fix
    for (Term t: list) {
//      System.out.println();
//      System.out.println(qvr + " " + Expression.old(qvr));
      final QuantVariableRef qvr = (QuantVariableRef) t;
      normalPost = new Post(normalPost.getRVar(),
                            normalPost.subst(Expression.old(qvr), qvr));
      excpPost = new Post(excpPost.getRVar(),
                            excpPost.subst(Expression.old(qvr), qvr));
//      System.out.println(normalPost);
    }
    // end momentary fix 
    out.incTab();
    out.println("" + Formula.generateFormulas(normalPost.getPost()));
    out.decTab();
    if (hasRet) {
      out.println("| Normal None => True");
    }
    else {
      out.println("| Normal (Some _) => True");
    }
    out.println("| Exception " + 
                              Formula.generateFormulas(excpPost.getRVar()) + 
                                       " =>");
    out.incTab();
    out.println("" + Formula.generateFormulas(
                                       excpPost.substWith(
                                              Ref.fromLoc(excpPost.getRVar()))));
    out.decTab();
    out.println("end.");
    out.decTab();
    out.decTab();
    
    // definition of the usable version
    out.definitionStart(namePost + " (s0:InitState) (t:ReturnState)", "list Prop");
    out.incPrintln();
    final String vars = doLetPost();
    out.incTab();
    //out.println(tab, "   let " + Ref.varThis + " := (do_lvget (fst s0) 0%N)" + " in " +
    out.println("(mk_" + namePost +  " (snd t) " + vars + "):: nil.");
    out.decTab();
    out.decTab();
    
  }
  
  /**
   * Returns the let expression used to define pre, using the predicate
   * mk_pre.
   * @return a string representing the let expression
   */
  private String doLetPre() {
    final CoqStream out = getAnnotationOut();
    String vars = "";
    final String hname = Formula.generateFormulas(Heap.var).toString();
    out.println("let " + hname + " := (snd s0) " + " in");
    vars += hname;
    int count = 0;
    for (Term qvr: Lookup.getInst().getPreconditionArgsWithoutHeap(fMeth)) {
      final String vname = Formula.generateFormulas(qvr).toString();
      out.println("let " + vname + " := " +
                           "(do_lvget (fst s0) " + count++ + "%N)" + " in ");
      vars += " " + vname;
    }
    return vars;
  }
  
  /**
   * Returns the let expression used to define post, using the predicate
   * mk_post.
   * @return a string representing the let expression
   */
  private String doLetPost() {
    final CoqStream out = getAnnotationOut();
    String vars = "";
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    out.println("let " + olhname + " := (snd s0) " + " in");
    vars += olhname;
    
    final String hname = Formula.generateFormulas(Heap.var).toString();
    out.println("let " + hname + " := (fst t) " + " in");
    vars += " " + hname;
    
    int count = 0;
    final LinkedList<Term> args = new LinkedList<Term>();
    args.addAll(Lookup.getInst().getPreconditionArgs(fMeth));
    args.removeFirst();
    for (Term qvr: args) {
      final String vname = Formula.generateFormulas(qvr).toString();
      out.println("let " + vname + " := " +
                           "(do_lvget (fst s0) " + count++ + "%N)" + " in ");
      vars += " " + vname;
    }
    
    return vars;
  }
  
}
