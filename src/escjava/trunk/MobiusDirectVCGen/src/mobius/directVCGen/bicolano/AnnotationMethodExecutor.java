package mobius.directVCGen.bicolano;

import java.util.List;
import java.util.Vector;

import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.RoutineDecl;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.Type;

import escjava.sortedProver.Lifter.QuantVariableRef;

import mobius.bico.ABasicExecutor;
import mobius.bico.MethodHandler;
import mobius.bico.Util.Stream;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.vcgen.struct.Post;

public class AnnotationMethodExecutor extends ABasicExecutor {
  /** the current routine (method) that is treated - esc java style. */
  private final RoutineDecl fRout;
  /** the current method (routine) that is treated - bcel style. */
  private final Method fMeth;

  public AnnotationMethodExecutor(ABasicExecutor be, final Method met, final RoutineDecl rout) {
    super(be);
    fRout = rout;
    fMeth = met;
  }

  @Override
  public void start() {
    doMethodPreAndPostDefinition();
  }
  
  private void doMethodPreAndPostDefinition() {
    final MethodHandler hdl = getMethodHandler();
    final String name = hdl.getName(fMeth);
    int tab = 1;
    final String nameModule = name + "_annotations";
    final String namePre = "pre";
    final String namePost = "post";
    final String nameAssertion = "assertion";
    final String nameAssumption = "assumption";
    final String nameSpec = "spec";
    final String defaultSpecs = "(0%nat,,(" + namePre + ",," + namePost + "))";

    final Stream out = getOut();
//    out.println(tab, "Definition " + namePost + " (s0:InitState) (t:ReturnState) := " +
//                        " @nil Prop.\n");
    out.println(tab, "Module " + nameModule + ".");
    tab++;
    doMethodPre(tab, namePre);
    doMethodPost(tab, namePost);
    out.println(tab, "Definition " + nameAssertion + " := " +
                AnnotationVisitor.getAssertion(fRout, fMeth) + ".");
    out.println(tab, "Definition " + nameAssumption + " :=" +
                  " (@PCM.empty Assumption).");
    out.println(tab, "Definition " + nameSpec + " :="); 
    out.println(tab + 1, "(" + defaultSpecs + ",,");
    out.println(tab + 2, "@PCM.empty (R.Assertion ** nat)). ");
    tab--;
    out.println(tab, "End " + nameModule + ".\n\n");
    
    
  }
  
  private void doMethodPre(final int tab, final String namePre) {
    final Stream out = getOut();
    out.println(tab, "Definition mk_" + namePre + " := ");
    final List<QuantVariableRef> list = mkArguments(fRout, fMeth);
    
    String varsAndType = "";
    final String hname = Formula.generateFormulas(Heap.var).toString();
    varsAndType += "(" + hname + ": " + Formula.generateType(Heap.var.getSort()) +  ")";
        
    for (QuantVariableRef qvr: list) {
      final String vname = Formula.generateFormulas(qvr).toString();
      varsAndType += " (" + vname + ": " + Formula.generateType(qvr.getSort()) +  ")";
      
    }
    out.println(tab + 1, "fun " + varsAndType + " => ");
    out.println(tab + 2, Formula.generateFormulas(Lookup.precondition(fRout)) + ".");
    out.println(tab, "Definition " + namePre + " (s0:InitState) := ");
    final String vars = doLetPre(tab + 1);
    
    //out.println(tab, "   let " + Ref.varThis + " := (do_lvget (fst s0) 0%N)" + " in " +
    out.println(tab + 2,  "mk_" + namePre +  " " + vars + ".");
    
  }
  
  
  private void doMethodPost(final int inittab, final String namePost) {
    final Stream out = getOut();
    int tab = inittab;
    
    // definition of the mk method
    out.println(tab, "Definition mk_" + namePost + " := ");
    final List<QuantVariableRef> list = mkOldArguments(fRout, fMeth);
    
    String varsAndType = "";
    
    
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    varsAndType += "(" + olhname + ": " + Formula.generateType(Heap.varPre.getSort()) +  ")";
    
    final String hname = Formula.generateFormulas(Heap.var).toString();
    varsAndType += "(" + hname + ": " + Formula.generateType(Heap.var.getSort()) +  ")";
    
    
    for (QuantVariableRef qvr: list) {
      final String vname = Formula.generateFormulas(qvr).toString();

      varsAndType += " (" + vname + ": " + Formula.generateType(qvr.getSort()) +  ")";
      
    }
        
    final Post normalPost = Lookup.normalPostcondition(fRout);
    final Post excpPost = Lookup.exceptionalPostcondition(fRout);
    tab++;
    out.println(tab, "fun " + "(t: ReturnVal) " + varsAndType + " => ");
    out.println(tab + 1, "match t with");
    final boolean hasRet = !(fMeth.getReturnType().equals(Type.VOID));
    
    if (hasRet) {
      out.println(tab + 1, "| Normal (Some " + 
                                       Formula.generateFormulas(normalPost.getRVar()) + 
                                       ") =>");
    }
    else {
      out.println(tab + 1, "| Normal None =>");
    }
    out.println(tab + 2, "" + Formula.generateFormulas(normalPost.getPost()));
    if (hasRet) {
      out.println(tab + 1, "| Normal None => True");
    }
    else {
      out.println(tab + 1, "| Normal (Some _) => True");
    }
    out.println(tab + 1, "| Exception " + 
                              Formula.generateFormulas(excpPost.getRVar()) + 
                                       " =>");
    out.println(tab + 2, "" + Formula.generateFormulas(
                                       excpPost.substWith(
                                              Ref.fromLoc(excpPost.getRVar()))));
    out.println(tab + 1, "end" + ".");
    tab--;

    // definition of the usable version
    out.println(tab, "Definition " + namePost + " (s0:InitState) (t:ReturnState) := ");
    final String vars = doLetPost(tab + 1);
    
    //out.println(tab, "   let " + Ref.varThis + " := (do_lvget (fst s0) 0%N)" + " in " +
    out.println(tab + 2,  "mk_" + namePost +  " (snd t) " + vars + ".");
    
  }
  
  private String doLetPre(final int tab) {
    final Stream out = getOut();
    String vars = "";
    final String hname = Formula.generateFormulas(Heap.var).toString();
    out.println(tab, "let " + hname + " := (snd s0) " + " in");
    vars += hname;
    int count = 0;
    for (QuantVariableRef qvr: mkArguments(fRout, fMeth)) {
      final String vname = Formula.generateFormulas(qvr).toString();
      out.println(tab, "let " + vname + " := " +
                           "(do_lvget (fst s0) " + count++ + "%N)" + " in ");
      vars += " " + vname;
    }
    return vars;
  }
  private String doLetPost(final int tab) {
    final Stream out = getOut();
    String vars = "";
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    out.println(tab, "let " + olhname + " := (snd s0) " + " in");
    vars += olhname;
    
    final String hname = Formula.generateFormulas(Heap.var).toString();
    out.println(tab, "let " + hname + " := (fst t) " + " in");
    vars += " " + hname;
    
    int count = 0;
    for (QuantVariableRef qvr: mkOldArguments(fRout, fMeth)) {
      final String vname = Formula.generateFormulas(qvr).toString();
      out.println(tab, "let " + vname + " := " +
                           "(do_lvget (fst s0) " + count++ + "%N)" + " in ");
      vars += " " + vname;
    }
    
    return vars;
  }
  
  public static List<QuantVariableRef> mkOldArguments(final RoutineDecl rd, Method met) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    final FormalParaDeclVec fpdvec = rd.args;
    if (!met.isStatic()) {
      v.add(Ref.varThis);
      
    }
    final FormalParaDecl[] args = fpdvec.toArray();
    for (FormalParaDecl fpd: args) {
      v.add(Expression.rvar(fpd));
    }
    return v;
  }
  
  public static List<QuantVariableRef> mkArguments(final RoutineDecl rd, Method met) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    final FormalParaDeclVec fpdvec = rd.args;
    if (!met.isStatic()) {
      v.add(Ref.varThis);
    }
    final FormalParaDecl[] args = fpdvec.toArray();
    for (FormalParaDecl fpd: args) {
      v.add(Expression.rvar(fpd));
    }
    return v;
  }

}
