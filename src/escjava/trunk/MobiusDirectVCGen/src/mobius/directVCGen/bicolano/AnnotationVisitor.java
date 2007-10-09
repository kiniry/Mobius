package mobius.directVCGen.bicolano;

import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import javafe.ast.ASTNode;
import javafe.ast.BlockStmt;
import javafe.ast.RoutineDecl;
import javafe.ast.VarDeclStmt;
import javafe.util.Location;
import mobius.bico.Util.Stream;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.vcgen.ABasicVisitor;

import org.apache.bcel.classfile.LineNumber;
import org.apache.bcel.classfile.LineNumberTable;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.Method;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;


/**
 * This class generates the annotations for Coq, in order
 * to mix them with bico.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class AnnotationVisitor extends ABasicVisitor {
  /** the Coq type of the assertions. */
  private static final String assertionType = "(InitState -> LocalState -> list Prop)";
  /** the Coq representation of an empty assertion. */
  private static final String assertionEmpty = "(PCM.empty (" + assertionType + " " +
                                                              "** nat))";
  /** the decorator that add the annotations or read the annotations from a node. */
  private final AnnotationDecoration fAnnot = AnnotationDecoration.inst;

  
  /** the currently treated method. */
  private final Method fMet;
  
  /** the arguments of the method. */
  private List<QuantVariableRef> fArgs;
  
  /** the local variables. */
  private LinkedList<List<QuantVariableRef>> fLocalVars = new LinkedList<List<QuantVariableRef>> ();
  
  /** the output file. */
  private final Stream fOut;
  
  /** the invariants counter. */
  private int fInvCounter = 1;
  
  /**
   * Create an annotation visitor targetting a specific method.
   * @param out 
   * @param decl 
   * @param met the method to inspect
   */
  private AnnotationVisitor(final Stream out, 
                            final RoutineDecl decl, 
                            final Method met) {
    fOut = out;
    fMet = met;
    fArgs = AnnotationMethodExecutor.mkArguments(decl, met);

  }



  @Override
  public /*@non_null*/ Object visitBlockStmt(final /*@non_null*/ BlockStmt x, final Object o) {
    fLocalVars.addLast(new Vector<QuantVariableRef>());
    final Object res = visitASTNode(x, o);
    fLocalVars.removeLast();
    return res;
  }
  


  public Object visitASTNode(final ASTNode x, final Object o) {
    String res = (String)o;
    
    
    if (fAnnot.getAnnotPost(x) != null) {
      // let's do something
//      System.out.println("post " + Location.toLineNumber(x.getStartLoc()) + ": " + 
//                         fAnnot.getAnnotPost(x));
    }
    if (fAnnot.getAnnotPre(x) != null) {
      // let's do something else
//      System.out.println("pre " + Location.toLineNumber(x.getStartLoc()) + ": " + 
//                         fAnnot.getAnnotPre(x));

    }
    if (fAnnot.getInvariant(x) != null) {
   
      // let's do a third thing
      final int lineNum = Location.toLineNumber(x.getStartLoc());
      final LineNumber line = getLineNumberFromLine(lineNum);
      final Term t = fAnnot.getInvariant(x);
      final List<LocalVariable> list = getValidVariables(getLineNumbers(lineNum));
      final List<QuantVariableRef> flat = flattenLocals();
      final String invName = "invariant" + fInvCounter++; 
      buildMker(invName, t, flat);
      buildDefiner(invName, t, flat);
      if (list.size() != flat.size()) {
        System.out.println(list + " " + fLocalVars);
      }
      res = "(PCM.update " + res + " " + line.getStartPC() + "%N" +
                     " (" + invName + ",," +  
                            fMet.getCode().getAttributes() + "%nat))";
    }
    
    final int max = x.childCount();

    for (int i = 0; i < max; i++) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        res = (String) ((ASTNode) child).accept(this, res);
      }
    }
    return res;
  }
 
  private void buildDefiner(String name, Term t, List<QuantVariableRef> flat) {
    String lets = "";
    String vars = "";
    // olds
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    lets += "let " + olhname + " := (snd s0) in \n";
    vars += olhname;
    int varcount = 0;
    for (QuantVariableRef qvr: fArgs) {
      varcount++;
      if (qvr.qvar.name.equals("this")) {
        continue;
      }
      final String vname = Formula.generateFormulas(Expression.old(qvr)).toString();
      lets += "let " + vname + " := (do_lvget (fst s0) " + varcount + "%N) in ";
      vars += " " + vname;
    }  
    lets += "\n";
    
    // new :)
    final String hname = Formula.generateFormulas(Heap.var).toString();
    lets += "let " + hname + " :=  (fst (fst s)) in \n";
    vars += " " + hname;
    varcount = 0;
    for (QuantVariableRef qvr: fArgs) {
      varcount++;
      final String vname = Formula.generateFormulas(qvr).toString();
      lets += "let " + vname + " := (do_lvget (snd s) " + varcount + "%N) in \n";
      vars += " " + vname;
    }
    for (QuantVariableRef qvr: flat) {
      varcount++;
      final String vname = Formula.generateFormulas(qvr).toString();
      lets += "let " + vname + " := (do_lvget (snd s) " + varcount + "%N) in \n";
      
      vars += " " + vname;
    }
    fOut.println("Definition " + name + " (s0:InitState) (s:LocalState): list Prop := ");
    fOut.incTab();
    fOut.println("(" + lets + "  mk_" + name + " " +  vars + "):: nil.");
    fOut.decTab();
  }



  private void buildMker(final String name, final Term body, List<QuantVariableRef> flat) {
    String varsAndType = "";
    // olds
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    varsAndType += "(" + olhname + ": " + Formula.generateType(Heap.varPre.getSort()) +  ") ";
    for (QuantVariableRef qvr: fArgs) {
      if (qvr.qvar.name.equals("this")) {
        continue;
      }
      final String vname = Formula.generateFormulas(Expression.old(qvr)).toString();
      varsAndType += "(" + vname + ": " + Formula.generateType(qvr.getSort()) +  ") ";
      
    }  
    varsAndType += "\n    ";
    
    // new :)
    final String hname = Formula.generateFormulas(Heap.var).toString();
    varsAndType += "(" + hname + ": " + Formula.generateType(Heap.var.getSort()) +  ") ";
     
    for (QuantVariableRef qvr: fArgs) {
      final String vname = Formula.generateFormulas(qvr).toString();
      varsAndType += "(" + vname + ": " + Formula.generateType(qvr.getSort()) +  ") ";
      
    }
    varsAndType += "\n    ";
    for (QuantVariableRef qvr: flat) {
      final String vname = Formula.generateFormulas(qvr).toString();
      varsAndType += "(" + vname + ": " + Formula.generateType(qvr.getSort()) +  ") ";
      
    }
    
    fOut.println("Definition mk_" + name + ":= ");
    fOut.incTab();
    fOut.println("fun " + varsAndType + "=> \n" + 
                   Formula.generateFormulas(body) + ".");
    fOut.decTab();
  }



  private List<QuantVariableRef> flattenLocals() {
    List<QuantVariableRef> res = new LinkedList<QuantVariableRef>();
    for (List<QuantVariableRef> list: fLocalVars) {
      res.addAll(list);
    }
    return res;
  }



  public List<LocalVariable> getValidVariables(List<LineNumber> lines) {
    final List<LocalVariable> res = new Vector<LocalVariable>();
    final LocalVariable[] lvt = fMet.getCode().getLocalVariableTable().getLocalVariableTable();
    int skip = fArgs.size(); // we skip the n first variables
   
    for (LocalVariable local: lvt) {
      if (skip > 0) {
        skip--;
      }
      else if (belongs(local, lines)) {
        
        res.add(local);
      }
    }
    return res;
  }
  private boolean belongs(LocalVariable local, List<LineNumber> lines) {
    for (LineNumber line: lines) {
      if ((line.getStartPC() >= local.getStartPC()) &&
          (line.getStartPC() <= local.getStartPC() + local.getLength())) {
        return true;
      }
    }
    return false;
  }







  public LineNumber getLineNumberFromLine(int lineNum) {
    final LineNumberTable lnt = fMet.getCode().getLineNumberTable();
    final LineNumber [] tab = lnt.getLineNumberTable();
    if (tab.length == 0) {
      return null;
    }
    LineNumber min = tab[0];
    int oldspan = Math.abs(min.getLineNumber() - lineNum);
    
    for (LineNumber line: tab) {
      final int span = (Math.abs(line.getLineNumber() - lineNum));
      if (span  > 0) {
        if (span < oldspan) {
          min = line;
          oldspan = span;
        }
      }
    }
    return min;
  }
  public /*@non_null*/ Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, 
                                               final Object o) {
    fLocalVars.getLast().add(Expression.rvar(x.decl));
    return o;
  }
  public List<LineNumber> getLineNumbers(int lineNum) {
    final List<LineNumber> res = new Vector<LineNumber>();
    final LineNumber first = getLineNumberFromLine(lineNum);
    final LineNumberTable lnt = fMet.getCode().getLineNumberTable();
    final LineNumber [] tab = lnt.getLineNumberTable();
    
    for (LineNumber line: tab) {
      if (line.getLineNumber() == first.getLineNumber()) {
        res.add(line);
      }
    }
    return res;
  }
  
  public static String getAssertion(final Stream out, final RoutineDecl decl, final Method met) {
    final String res = (String) decl.accept(new AnnotationVisitor(out, decl, met),  
                         assertionEmpty);
    return res;
  }
  
}
