package mobius.directVCGen.vcgen.wp;

import javafe.ast.ASTNode;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;

/**
 * This visitor gives the basic functionnality of the expression vc gen(s).
 * It is made to be subclassed as a vcgen, coupled with an expression visitor. 
 * The sole purpose of this class is to contain standard functions. 
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class ABasicExpressionVCGEn {
  /** the visitor coupled with this vcgen. */
  private ExpressionVisitor fVisitor;

  /**
   * The basic constructor which initialize the vcgen with a visitor.
   * @param visitor the visitor associated with this vcgen
   */
  public ABasicExpressionVCGEn(final ExpressionVisitor visitor) {
    fVisitor = visitor;
    if (fVisitor == null) {
      throw new NullPointerException("The visitor cannot be null!");
    }
  }

  /**
   * Return the precondition calculated by the vcgen for the given postcondition.
   * The sole interest of this methodis to type the loosy-typed visitor pattern :)
   * @param x the node to visit
   * @param entry the current postcondition associated with the instruction
   * @return a precondition calculated by the vc gen
   */
  public Post getPre(final ASTNode x, final VCEntry entry) {
    return (Post)x.accept(fVisitor, entry);
  }





}
