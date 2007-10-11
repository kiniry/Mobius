package mobius.directVCGen.bicolano;

import java.util.Iterator;
import java.util.List;

import javafe.ast.ASTNode;
import javafe.ast.RoutineDecl;
import javafe.util.Location;
import mobius.bico.Util.Stream;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.vcgen.ABasicVisitor;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
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
  

  /** the output file. */
  private final Stream fOut;
  
  
  /**
   * Create an annotation visitor targetting a specific method.
   * @param out the file where to output the annotations
   * @param decl the routine which is currently inspected
   * @param met the method to inspect
   */
  private AnnotationVisitor(final Stream out, 
                            final RoutineDecl decl, 
                            final MethodGen met) {
    fOut = out;
    fMet = met;


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
      final List<LineNumberGen> lineList = Util.getLineNumbers(fMet, lineNum);
      final Term t = fAnnot.getInvariant(x);
      
      final String invName = fAnnot.getInvariantName(x); 
      buildMker(invName, t, fAnnot.getInvariantArgs(x));
      buildDefiner(invName, fAnnot.getInvariantArgs(x));
      

      final InstructionHandle ih = Util.findLastInstruction(lineList);
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
 

  /**
   * Define the annotations for the bytecide with the right local variables.
   * @param name the name of the annotation do define
   * @param listVar the list of variables used in the annotation
   */
  private void buildDefiner(final String name, final List<QuantVariableRef> listVar) {
    String lets = "";
    String vars = "";
    final Iterator<QuantVariableRef> iter = listVar.iterator();
    QuantVariableRef var;
    // olds
    var = iter.next(); // the old heap
    final String olhname = Formula.generateFormulas(var).toString();
    lets += "let " + olhname + " := (snd s0) in \n";
    vars += olhname;
    
    // now the variables
    int varcount = 0;
    var = iter.next();
    while (!var.equals(Heap.var)) {
      varcount++;
      final String vname = Formula.generateFormulas(var).toString();
      lets += "let " + vname + " := (do_lvget (fst s0) " + varcount + "%N) in ";
      vars += " " + vname;
      var = iter.next();
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
      varcount++;
      final String vname = Formula.generateFormulas(var).toString();
      lets += "let " + vname + " := (do_lvget (snd s) " + varcount + "%N) in \n";
      vars += " " + vname;
    }
    
    fOut.println("Definition " + name + " (s0:InitState) (s:LocalState): list Prop := ");
    fOut.incTab();
    fOut.println("(" + lets + "  mk_" + name + " " +  vars + "):: nil.");
    fOut.decTab();
  }


  /**
   * Write the base definition of an assertion. The name used is of the form
   * <code>mk_</code>
   * @param name the name of the assertion
   * @param body the body of the assertion
   * @param varList the list of the variables used
   */
  private void buildMker(final String name, final Term body, 
                         final List<QuantVariableRef> varList) {
    String varsAndType = "";
    for (QuantVariableRef qvr: varList) {
      final String vname = Formula.generateFormulas(qvr).toString();
      varsAndType += "(" + vname + ": " + Formula.generateType(qvr.getSort()) +  ") ";
      
    }
    fOut.println("Definition mk_" + name + ":= ");
    fOut.incTab();
    fOut.println("fun " + varsAndType + "=> \n" + 
                   Formula.generateFormulas(body) + ".");
    fOut.decTab();
  }

  

  
  /**
   * Returns the assertion enumeration.
   * @param out the file to dump the assertion definition to
   * @param decl the method to inspect, from ESC/Java
   * @param met the method to inspect, from BCEL
   * @return an enumeration of assertions
   */
  public static String getAssertion(final Stream out, final RoutineDecl decl, final MethodGen met) {
    final String res = (String) decl.accept(new AnnotationVisitor(out, decl, met),  
                         assertionEmpty);
    return res;
  }
  
}
