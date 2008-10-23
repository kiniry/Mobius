package mobius.directVCGen.bico;

import java.util.Iterator;
import java.util.List;

import javafe.util.Location;
import mobius.bico.bicolano.coq.CoqStream;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.PositionHint;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.LineNumberGen;
import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariableRef;


/**
 * This class generates the annotations for Coq, in order
 * to mix them with bico.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class AnnotationVisitor {
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
  


  /**
   * Create an annotation visitor targetting a specific method.
   * @param out the file where to output the annotations
   * @param decl the routine which is currently inspected
   * @param met the method to inspect
   */
  private AnnotationVisitor(final CoqStream out, 
                            //final RoutineDecl decl, 
                            final MethodGen met) {
    fOut = out;
    fMet = met;
    

  }

  /** {@inheritDoc} */

  public String start() {
    InstructionList il = fMet.getInstructionList();
    String res = assertionEmpty;
    
    for(InstructionHandle ih: il.getInstructionHandles()) {
      PositionHint hint = new PositionHint(ih);
      if (fAnnot.getAnnotPost(hint) != null) {
        // let's do something
        System.err.println("Post annotation are unhandled at the moment.");
      }
      if (fAnnot.getAnnotPre(hint) != null) {
        // let's do something else
        //final int lineNum = Location.toLineNumber(x.getStartLoc());
        //final List<LineNumberGen> lineList = Util.getLineNumbers(fMet, lineNum);
        final List<AAnnotation> list = fAnnot.getAnnotPre(hint);
        for (AAnnotation annot: list) {
          buildMker(annot);
          buildDefiner(annot);      
        }
      }
      if (fAnnot.getInvariant(hint) != null) {
        // let's do a third thing
        final int lineNum = Location.toLineNumber(hint.getStartLoc());
        final List<LineNumberGen> lineList = Util.getLineNumbers(fMet, lineNum);
        final AAnnotation inv = fAnnot.getInvariant(hint);
        buildMker(inv);
        buildDefiner(inv);
        

        final InstructionHandle last = Util.findLastInstruction(lineList);
        res = "(PCM.update " + res + " " + last.getPosition() + "%N" +
                      " (" + inv.getName() + ",," +  
                          fMet.getInstructionList().getEnd().getPosition() + "%nat))";
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
    final Iterator<QuantVariableRef> iter = annot.getArgs().iterator();
    QuantVariableRef var;
    // olds
    var = iter.next(); // the old heap
    lets += "let " + Formula.generateFormulas(var) + " := (snd s0) in \n";
    
    // now the old variables
    int varcount = 1;
    var = iter.next();
    
    while (!var.equals(Heap.var)) {
      lets += "let " + Formula.generateFormulas(var) + " := " +
                 "(do_lvget (fst s0) " + varcount + "%N) in ";
      var = iter.next();
      varcount++;
    }  
    lets += "\n";
    
    // new heap :)
    lets += "let " + Formula.generateFormulas(var) + " :=  (fst (fst s)) in \n";
    
    // new variables
    varcount = 0;
    while (iter.hasNext()) {
      var = iter.next();
      lets += "let " + Formula.generateFormulas(var) + " := " +
                  "(do_lvget (snd s) " + varcount + "%N) in \n";
      varcount++;
    }
    
    fOut.incPrintln("Definition " + annot.getName() + " (s0:InitState) " +
        "(s:LocalState): list Prop := ");
    fOut.println("(" + lets + "  mk_" + annot.getName() + " " +  
                 getVarsName(annot) + "):: nil.");
    fOut.decTab();
  }

  /**
   * Returns a string containing the variable list that 
   * shall be the arguments for the annotation.
   * @param annot the annotation to inspect
   * @return a string containing the variables name separated by a space
   */
  private String getVarsName(final AAnnotation annot) {
    String vars = ""; 
    for (QuantVariableRef var: annot.getArgs()) {
      vars += " " + Formula.generateFormulas(var);
    }
    return vars.substring(1);
  }


  /**
   * Write the base definition of an assertion. The name used is of the form
   * <code>mk_</code>
   * @param annot the assertion to translate
   */
  private void buildMker(final AAnnotation annot) {
    String varsAndType = "";
    for (QuantVariableRef qvr: annot.getArgs()) {
      final String vname = Formula.generateFormulas(qvr).toString();
      varsAndType += "(" + vname + ": " + Formula.generateType(qvr.getSort()) +  ") ";
      
    }
    fOut.println("Definition mk_" + annot.getName() + ":= ");
    fOut.incTab();
    fOut.println("fun " + varsAndType + "=> \n" + 
                   Formula.generateFormulas(annot.getFormula()) + ".");
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
                                    final MethodGen met) {
    final AnnotationVisitor vis = new AnnotationVisitor(out, met);
    //VarCorrVisitor.annotateWithVariables(met);
    final String res = vis.start();
 
    return res;
  }
  
}
