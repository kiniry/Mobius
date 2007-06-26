package mobius.directVCGen.bicolano;

import java.util.List;
import java.util.Vector;

import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.RoutineDecl;

import org.apache.bcel.classfile.Method;

import escjava.sortedProver.Lifter.QuantVariableRef;

import mobius.bico.ABasicExecutor;
import mobius.bico.MethodHandler;
import mobius.bico.Util.Stream;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;

public class AnnotationMethodExecutor extends ABasicExecutor {

  private final RoutineDecl fRout;
  
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
    final int tab = 1;
    final String namePre = name + "_pre";
    final String namePost = name + "_post";
    final String nameAssertion = name + "_assertion";
    final String nameAssumption = name + "_assumption";
    final String defaultSpecs = "(0%nat,,(" + namePre + ",," + namePost + "))";

    doMethodPre(tab, namePre);
    final Stream out = getOut();
    out.println(tab, "Definition " + namePost + " (s0:InitState) (t:ReturnState) := " +
                        " @nil Prop.\n");
    
    
    out.println(tab, "Definition " + nameAssertion + " := " +
                AnnotationVisitor.getAssertion(fRout, fMeth) + ".");
    out.println(tab, "Definition " + nameAssumption + " :=" +
                  " (@PCM.empty Assumption).");
    out.println(tab, "Definition " + name + "_spec :="); 
    out.println(tab + 1, "(" + defaultSpecs + ",,");
    out.println(tab + 2, "@PCM.empty (R.Assertion ** nat)).\n\n ");

    
    
  }
  
  private void doMethodPre(final int tab, final String namePre) {
    final Stream out = getOut();
    out.println(tab, "Definition mk_" + namePre + " := ");
    List<QuantVariableRef> list = mkArguments(fRout, fMeth);
    String vars = "";
    String varsAndType = "";
    final String hname = Formula.generateFormulas(Heap.var).toString();
    vars += hname;
    varsAndType += "(" + hname + ": " + Formula.generateType(Heap.var.getSort()) +  ")";
        
    for (QuantVariableRef qvr: list) {
      final String vname = Formula.generateFormulas(qvr).toString();
      vars += " " + vname;
      varsAndType += " (" + vname + ": " + Formula.generateType(qvr.getSort()) +  ")";
      
    }
    out.println(tab + 1, "fun " + varsAndType + " => ");
    out.println(tab + 2, Formula.generateFormulas(Lookup.precondition(fRout)).toString() + ".");
    out.println(tab, "Definition " + namePre + " (s0:InitState) := ");
    doLet(tab + 1);
    
    //out.println(tab, "   let " + Ref.varThis + " := (do_lvget (fst s0) 0%N)" + " in " +
    out.println(tab + 2,  "mk_" + namePre +  " " + vars + ".");
    
  }
  
  
  private String doLet(final int tab) {
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
