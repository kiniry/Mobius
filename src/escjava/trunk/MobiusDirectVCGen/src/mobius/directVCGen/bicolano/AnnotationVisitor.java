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
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.vcgen.ABasicVisitor;

import org.apache.bcel.classfile.LineNumber;
import org.apache.bcel.classfile.LineNumberTable;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;

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
  private final MethodGen fMet;
  
  /** the arguments of the method. */
  private LinkedList<Term> fArgs;
  
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
                            final MethodGen met) {
    fOut = out;
    fMet = met;
    fArgs = new LinkedList<Term>(); 
    fArgs.addAll(Lookup.getInst().getPreconditionArgs(decl));
    fArgs.removeFirst();

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
      final LineNumberGen line = getLineNumberFromLine(lineNum);
      final List<LineNumberGen> lineList = getLineNumbers(lineNum);
      final Term t = fAnnot.getInvariant(x);
      final List<LocalVariableGen> list = getValidVariables(getLineNumbers(lineNum));
      final List<QuantVariableRef> flat = flattenLocals();
      final String invName = "invariant" + fInvCounter++; 
      buildMker(invName, t, flat);
      buildDefiner(invName, t, flat);
      if (list.size() != flat.size()) {
        System.out.println(list + " " + fLocalVars);
      }
      
//      res = "(PCM.update " + res + " " + line.getInstruction().getPosition() + "%N" +
//                     " (" + invName + ",," +  
//                            fMet.getInstructionList().size() + "%nat))";
      final InstructionHandle ih = findLastInstruction(lineList);
      res = "(PCM.update " + res + " " + ih.getPosition() + "%N" +
                    " (" + invName + ",," +  
                        fMet.getInstructionList().getEnd().getPosition() + "%nat))";
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
 
  private InstructionHandle findLastInstruction(List<LineNumberGen> list) {
    final InstructionHandle baseih = list.get(0).getInstruction();
    InstructionHandle ih = baseih.getNext();
    
    //return ih;
    // first we find the first goto

    while (!(ih.getInstruction() instanceof GotoInstruction)) {
      ih = ih.getNext();
    }
    final GotoInstruction bi =  (GotoInstruction) ih.getInstruction();
    return bi.getTarget();
//    
//    while (ofthisline == false) {
//      System.out.println(ih + "???");
//      ofthisline = false; 
//      for (LineNumberGen line : list) {
//        ofthisline |= line.containsTarget(ih);
//      }
//      ih = ih.getNext();
//    }
//    return ih.getPrev();
//    while (ih != baseih) {
//      if (ih.getInstruction() instanceof BranchInstruction) {
//
//        final BranchInstruction bi =  (BranchInstruction) ih.getInstruction();
//        for (LineNumberGen line : list) {
//          line.containsTarget(bi.getTarget());
//          return ih.getPrev();
//        }
//        System.out.println(baseih + "???" + ih + " ??"  + 
//                           baseih.getTargeters()[0] + 
//                           list.containsTarget(bi.getTarget()));
//        if (bi.getTarget().equals(baseih) || bi.getTarget().equals(baseih.getNext())) {
//          return ih.getPrev();
//        }
//      }    
//      ih = ih.getNext();
//    }
//    return ih;
  }



  private void buildDefiner(String name, Term t, List<QuantVariableRef> flat) {
    String lets = "";
    String vars = "";
    // olds
    final String olhname = Formula.generateFormulas(Heap.varPre).toString();
    lets += "let " + olhname + " := (snd s0) in \n";
    vars += olhname;
    int varcount = 0;
    for (Term ter: fArgs) {
      varcount++;
      final QuantVariableRef qvr = (QuantVariableRef) ter;
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
    for (Term qvr: fArgs) {
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
    for (Term t: fArgs) {
      QuantVariableRef qvr = (QuantVariableRef) t;
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
     
    for (Term qvr: fArgs) {
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



  public List<LocalVariableGen> getValidVariables(List<LineNumberGen> lines) {
    final List<LocalVariableGen> res = new Vector<LocalVariableGen>();
    final LocalVariableGen[] lvt = fMet.getLocalVariables();
    int skip = fArgs.size(); // we skip the n first variables
   
    for (LocalVariableGen local: lvt) {
      if (skip > 0) {
        skip--;
      }
      else if (belongs(local, lines)) {
        
        res.add(local);
      }
    }
    return res;
  }
  private boolean belongs(LocalVariableGen local, List<LineNumberGen> lines) {
     
    for (LineNumberGen line: lines) {
      final int linePc = line.getLineNumber().getStartPC();
      final int localPc = local.getStart().getPosition();
      if ((linePc >= localPc) &&
          (line.getLineNumber().getStartPC() <= localPc + local.getStart().getPosition())) {
        return true;
      }
    }
    return false;
  }







  public LineNumberGen getLineNumberFromLine(int lineNum) {
    final LineNumberGen [] tab = fMet.getLineNumbers();
    if (tab.length == 0) {
      return null;
    }
    LineNumberGen min = tab[0];
    int oldspan = Math.abs(min.getSourceLine() - lineNum);
    
    for (LineNumberGen line: tab) {
      final int span = (Math.abs(line.getSourceLine() - lineNum));
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
  public List<LineNumberGen> getLineNumbers(int lineNum) {
    final List<LineNumberGen> res = new Vector<LineNumberGen>();
    final LineNumberGen first = getLineNumberFromLine(lineNum);
    final LineNumberGen [] tab = fMet.getLineNumbers();
//    final LineNumber [] tab = lnt.getLineNumberTable();
    
    for (LineNumberGen line: tab) {
      if (line.getLineNumber().getLineNumber() == first.getLineNumber().getLineNumber()) {
        res.add(line);
      }
    }
    return res;
  }
  
  public static String getAssertion(final Stream out, final RoutineDecl decl, final MethodGen met) {
    final String res = (String) decl.accept(new AnnotationVisitor(out, decl, met),  
                         assertionEmpty);
    return res;
  }
  
}
