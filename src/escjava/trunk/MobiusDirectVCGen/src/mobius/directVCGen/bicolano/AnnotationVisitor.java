package mobius.directVCGen.bicolano;

import javafe.ast.ASTNode;
import javafe.ast.RoutineDecl;
import javafe.util.Location;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.vcgen.ABasicVisitor;

import org.apache.bcel.classfile.LineNumber;
import org.apache.bcel.classfile.LineNumberTable;
import org.apache.bcel.classfile.Method;

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
  private static final String assertionEmpty = "(@PCM.empty (" + assertionType + " " +
                                                              "** nat))";
  /** the decorator that add the annotations or read the annotations from a node. */
  private final AnnotationDecoration fAnnot = AnnotationDecoration.inst;

  
  /** the currently treated method. */
  private final Method fMet;

  /**
   * Create an annotation visitor targetting a specific method.
   * @param met the method to inspect
   */
  private AnnotationVisitor(final Method met) {
    fMet = met;
  }



  
  public Object visitASTNode(final ASTNode x, final Object o) {
    String res = (String)o;
    
    if (fAnnot.getAnnotPost(x) != null) {
      // let's do something
      System.out.println("post " + Location.toLineNumber(x.getStartLoc()) + ": " + 
                         fAnnot.getAnnotPost(x));
    }
    if (fAnnot.getAnnotPre(x) != null) {
      // let's do something else
      System.out.println("pre " + Location.toLineNumber(x.getStartLoc()) + ": " + 
                         fAnnot.getAnnotPre(x));

    }
    if (fAnnot.getInvariant(x) != null) {
      // let's do a third thing
      final LineNumberTable lnt = fMet.getCode().getLineNumberTable();
      final LineNumber [] tab = lnt.getLineNumberTable();
      final int lineNum = Location.toLineNumber(x.getStartLoc());
      int oldspan = tab.length;
      LineNumber min = null;
      for (LineNumber line: tab) {
        final int span = (line.getLineNumber() - lineNum);
        if (span  > 0) {
          if (span < oldspan) {
            min = line;
            oldspan = span;
          }
        }
        

      }
      if (min != null) {
        final Term t = fAnnot.getInvariant(x);
        res = "(PCM.update " + res + " " + min.getStartPC() + "%N" +
                     " (" + Formula.generateFormulas(t) + ",," +  
                            fMet.getCode().getLength() + "%nat))";
      }
      System.out.println("inv " +  lineNum +  ": " + 
                         fAnnot.getInvariant(x));
      
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
  
  
  public static String getAssertion(final RoutineDecl decl, final Method met) {
    return (String) decl.accept(new AnnotationVisitor(met),  
                                       assertionEmpty);  
  }
}
