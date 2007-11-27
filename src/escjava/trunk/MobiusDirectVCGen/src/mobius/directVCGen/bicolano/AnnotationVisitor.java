package mobius.directVCGen.bicolano;

import java.util.Iterator;
import java.util.List;

import javafe.ast.ASTNode;
import javafe.ast.RoutineDecl;
import javafe.util.Location;
import mobius.bico.coq.CoqStream;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.vcgen.ABasicVisitor;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariableRef;


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
  

  /** the output file. */
  private final CoqStream fOut;
  private List<QuantVariableRef> fVariables;
  


  /**
   * Create an annotation visitor targetting a specific method.
   * @param out the file where to output the annotations
   * @param decl the routine which is currently inspected
   * @param met the method to inspect
   */
  private AnnotationVisitor(final CoqStream out, 
                            final RoutineDecl decl, 
                            final MethodGen met) {
    fOut = out;
    fMet = met;
    

  }


  public /*@non_null*/ Object visitRoutineDecl(/*@non_null*/ RoutineDecl x, Object o) {
    if (x.body != null) {
      return x.body.accept(this, o);
    }
    return o;
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
      final int lineNum = Location.toLineNumber(x.getStartLoc());
      final List<LineNumberGen> lineList = Util.getLineNumbers(fMet, lineNum);
      final List<AAnnotation> list = fAnnot.getAnnotPre(x);
      for (AAnnotation annot: list) {
        buildMker(annot);
        buildDefiner(annot);      
      }
      
//      System.out.println("pre " + Location.toLineNumber(x.getStartLoc()) + ": " + 
//                         fAnnot.getAnnotPre(x));

    }
    if (fAnnot.getInvariant(x) != null) {
   
      // let's do a third thing
      final int lineNum = Location.toLineNumber(x.getStartLoc());
      final List<LineNumberGen> lineList = Util.getLineNumbers(fMet, lineNum);
      final AAnnotation inv = fAnnot.getInvariant(x);
      buildMker(inv);
      buildDefiner(inv);
      

      final InstructionHandle ih = Util.findLastInstruction(lineList);
      res = "(PCM.update " + res + " " + ih.getPosition() + "%N" +
                    " (" + inv.fName + ",," +  
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
 

  /**
   * Define the annotations for the bytecide with the right local variables.
   * @param annot the assertion to translate
   */
  private void buildDefiner(final AAnnotation annot) {
    String lets = "";
    String vars = "";
    final Iterator<QuantVariableRef> iter = annot.fArgs.iterator();
    QuantVariableRef var;
    // olds
    var = iter.next(); // the old heap
    final String olhname = Formula.generateFormulas(var).toString();
    lets += "let " + olhname + " := (snd s0) in \n";
    vars += olhname;
    
    // now the variables
    int varcount = 1;
    var = iter.next();
    
    while (!var.equals(Heap.var)) {
      final String vname = Formula.generateFormulas(var).toString();
      lets += "let " + vname + " := (do_lvget (fst s0) " + varcount + "%N) in ";
      vars += " " + vname;
      var = iter.next();
      varcount++;
    }  
    lets += "\n";
    
    // new :)
    final String hname = Formula.generateFormulas(var).toString();
    lets += "let " + hname + " :=  (fst (fst s)) in \n";
    vars += " " + hname;
    
    // new variables
    varcount = 0;
    while (iter.hasNext()) {
      var = iter.next();
      if (var.equals(Ref.varThis)) {
        final String vname = Formula.generateFormulas(var).toString();
        lets += "let " + vname + " := (do_lvget (snd s) " + varcount + "%N) in \n";
        vars += " " + vname;
      }
      else {
        final String vname = Formula.generateFormulas(var).toString();
        lets += "let " + vname + " := (do_lvget (snd s) " + varcount + "%N) in \n";
        vars += " " + vname;
      }
      varcount++;
    }
    
    fOut.println("Definition " + annot.fName + " (s0:InitState) " +
        "(s:LocalState): list Prop := ");
    fOut.incTab();
    fOut.println("(" + lets + "  mk_" + annot.fName + " " +  vars + "):: nil.");
    fOut.decTab();
  }


  /**
   * Write the base definition of an assertion. The name used is of the form
   * <code>mk_</code>
   * @param annot the assertion to translate
   */
  private void buildMker(final AAnnotation annot) {
    String varsAndType = "";
    for (QuantVariableRef qvr: annot.fArgs) {
      final String vname = Formula.generateFormulas(qvr).toString();
      varsAndType += "(" + vname + ": " + Formula.generateType(qvr.getSort()) +  ") ";
      
    }
    fOut.println("Definition mk_" + annot.fName + ":= ");
    fOut.incTab();
    fOut.println("fun " + varsAndType + "=> \n" + 
                   Formula.generateFormulas(annot.formula) + ".");
    fOut.decTab();
  }

  

  
  /**
   * Returns the assertion enumeration.
   * @param out the file to dump the assertion definition to
   * @param decl the method to inspect, from ESC/Java
   * @param met the method to inspect, from BCEL
   * @return an enumeration of assertions
   */
  public static String getAssertion(final CoqStream out, 
                                    final RoutineDecl decl, 
                                    final MethodGen met) {
    final AnnotationVisitor vis = new AnnotationVisitor(out, decl, met);
    vis.fVariables = VarCorrVisitor.getVariables(decl, met);
    final String res = (String) decl.accept(vis, assertionEmpty);
 
    return res;
  }
  
}
