package mobius.directVCGen.bicolano;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.RoutineDecl;
import javafe.ast.TypeModifierPragma;
import mobius.bico.Util.Stream;
import mobius.bico.dico.MethodHandler;
import mobius.bico.executors.ABasicExecutor;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.vcgen.struct.Post;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class AnnotationMethodExecutor extends ABasicExecutor {
  /** the current routine (method) that is treated - esc java style. */
  private final RoutineDecl fRout;
  /** the current method (routine) that is treated - bcel style. */
  private final MethodGen fMeth;
  
  /** the stream where to write the annotations. */
  private final Stream fAnnotOut;
  /** the class from which the inspected method is taken. */
  private ClassGen fClass;

  public AnnotationMethodExecutor(ABasicExecutor be, final Stream annotationOut, 
                                  ClassGen clzz, final Method met, final RoutineDecl rout) {
    super(be);
    if (rout == null) {
      throw new NullPointerException();
    }
    if (met == null) {
      throw new NullPointerException();
    }
    fRout = rout;
    fMeth = new MethodGen(met, clzz.getClassName(), clzz.getConstantPool());
    fClass = clzz;
    fAnnotOut = annotationOut;
  }

  @Override
  public void start() {
    Lookup.getInst().computePreconditionArgs();
    doMethodPreAndPostDefinition();
  }
  
  private void doMethodPreAndPostDefinition() {
    final MethodHandler hdl = getMethodHandler();
    final String name = hdl.getName(fMeth);
    final String nameModule = name;
    final String namePre = "pre";
    final String namePost = "post";
    final String nameAssertion = "assertion";
    final String nameAssumption = "assumption";
    final String nameSpec = "spec";
    int needed = 0;
    if (fMeth.getInstructionList() != null) {
      needed = fMeth.getInstructionList().getEnd().getPosition(); 
    }
    final String defaultSpecs = "(" +
             needed + 
            "%nat,,global_spec)";

    final Stream out = getAnnotationOut();
    
    out.println("Module " + nameModule + ".");
    out.incTab();
    
    // pre and post def
    doMethodPre(namePre);
    doMethodPost(namePost);
    out.println("Definition global_spec: GlobalMethSpec := (" + namePre + 
                " ,, " + namePost + ").\n");

    // assertion and assumption def
    
    out.println("Definition " + nameAssertion + " := " +
                AnnotationVisitor.getAssertion(out, fRout, fMeth) + ".");
    out.println("Definition " + nameAssumption + " :=" +
                  " (PCM.empty Assumption).");
    out.println("Definition local_spec: LocMethSpec := (" + nameAssertion + " ,, " + 
                nameAssumption + ").\n");
    
    // al together
    out.println("Definition " + nameSpec + " :=");
    out.incTab();
    out.println("(" + defaultSpecs + ",,local_spec). ");
    out.decTab();
    out.decTab();
    out.println("End " + nameModule + ".\n");
    
  }
  
  protected Stream getAnnotationOut() {
    return fAnnotOut;
  }

  private void doMethodPre(final String namePre) {
    final Stream out = getAnnotationOut();
    out.println("Definition mk_" + namePre + " := ");
    final List<QuantVariableRef> list = Lookup.getInst().getPreconditionArgs(fRout);
    
    String varsAndType = "";

    for (Term qvr: list) {
      final String vname = Formula.generateFormulas(qvr).toString();
      varsAndType += " (" + vname + ": " + Formula.generateType(qvr.getSort()) +  ")";
      
    }

    out.incTab();
    out.println("fun " + varsAndType + " => ");
    out.incTab();
    out.println(Formula.generateFormulas(Lookup.precondition(fRout)) + ".");
    out.decTab();
    out.decTab();
    out.println("Definition " + namePre + " (s0:InitState): list Prop := ");
    out.incTab();
    final String vars = doLetPre();
    out.incTab();
    //out.println(tab, "   let " + Ref.varThis + " := (do_lvget (fst s0) 0%N)" + " in " +
    out.println("(mk_" + namePre +  " " + vars + "):: nil.");
    out.decTab();
    out.decTab();
  }
  
  
  private void doMethodPost(final String namePost) {
    final Stream out = getAnnotationOut();
    // definition of the mk method
    out.println("Definition mk_" + namePost + " := ");
    final List<QuantVariableRef> list = Lookup.getInst().getPreconditionArgsWithoutHeap(fRout);
    
    String varsAndType = "";
    
    
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    varsAndType += "(" + olhname + ": " + Formula.generateType(Heap.varPre.getSort()) +  ")";
    
    final String hname = Formula.generateFormulas(Heap.var).toString();
    varsAndType += "(" + hname + ": " + Formula.generateType(Heap.var.getSort()) +  ")";
    
    
    for (Term qvr: list) {
      final String vname = Formula.generateFormulas(qvr).toString();

      varsAndType += " (" + vname + ": " + Formula.generateType(qvr.getSort()) +  ")";
      
    }
        
    Post normalPost = Lookup.normalPostcondition(fRout);
    final QuantVariableRef varRes = normalPost.getRVar();
    if (varRes != null) {
      final QuantVariableRef v = normalPost.getRVar();
      final Term f = Heap.valueToSort(v, varRes.getSort());
      //System.out.println(f);
      normalPost = new Post(v, normalPost.nonSafeSubst(v, f));
    }
    Post excpPost = Lookup.getExceptionalPostcondition(fRout);
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
    out.println("Definition " + namePost + " (s0:InitState) (t:ReturnState): " +
        "list Prop := ");
    out.incTab();
    final String vars = doLetPost();
    out.incTab();
    //out.println(tab, "   let " + Ref.varThis + " := (do_lvget (fst s0) 0%N)" + " in " +
    out.println("(mk_" + namePost +  " (snd t) " + vars + "):: nil.");
    out.decTab();
    out.decTab();
    
  }
  
  private String doLetPre() {
    final Stream out = getAnnotationOut();
    String vars = "";
    final String hname = Formula.generateFormulas(Heap.var).toString();
    out.println("let " + hname + " := (snd s0) " + " in");
    vars += hname;
    int count = 0;
    for (Term qvr: Lookup.getInst().getPreconditionArgsWithoutHeap(fRout)) {
      final String vname = Formula.generateFormulas(qvr).toString();
      out.println("let " + vname + " := " +
                           "(do_lvget (fst s0) " + count++ + "%N)" + " in ");
      vars += " " + vname;
    }
    return vars;
  }
  
  
  private String doLetPost() {
    final Stream out = getAnnotationOut();
    String vars = "";
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    out.println("let " + olhname + " := (snd s0) " + " in");
    vars += olhname;
    
    final String hname = Formula.generateFormulas(Heap.var).toString();
    out.println("let " + hname + " := (fst t) " + " in");
    vars += " " + hname;
    
    int count = 0;
    final LinkedList<Term> args = new LinkedList<Term>();
    args.addAll(Lookup.getInst().getPreconditionArgs(fRout));
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
