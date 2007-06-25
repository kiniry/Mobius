package mobius.directVCGen.bicolano;

import javafe.ast.ASTNode;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.vcgen.ABasicVisitor;

public class AnnotationVisitor extends ABasicVisitor {
  /** the decorator that add the annotations or read the annotations from a node. */
  private final AnnotationDecoration fAnnot = AnnotationDecoration.inst;
  
  public Object visitASTNode(final ASTNode x, final Object o) {
    //System.out.println(x);
    System.out.println("{ " + fAnnot.getAnnotPost(x) + 
                        " " + fAnnot.getAnnotPre(x) + " " + fAnnot.getInvariant(x));
    final int max = x.childCount();
    Object res = o;
    for (int i = 0; i < max; i++) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        res = ((ASTNode) child).accept(this, o);
      }
    }
    return res;
  }
}
