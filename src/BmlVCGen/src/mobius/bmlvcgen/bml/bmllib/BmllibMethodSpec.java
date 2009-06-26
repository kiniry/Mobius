package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.MethodSpec;
import mobius.bmlvcgen.bml.MethodSpecVisitor;
import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.util.Visitable;
import annot.attributes.method.SpecificationCase;

/**
 * Wrapper for bmllib method specification case.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class BmllibMethodSpec implements MethodSpec {
  // Wrapped precondition.
  private final Visitable<PreExprVisitor> pre;
  // Wrapped postcondition.
  private final Visitable<PostExprVisitor> post;

  
  /**
   * Constructor.
   * @param spec Specification to wrap.
   */
  public BmllibMethodSpec(final SpecificationCase spec) {
    final PreExprWrapper preWrapper = new PreExprWrapper();
    final PostExprWrapper postWrapper = 
      new PostExprWrapper(preWrapper);
    pre = preWrapper.wrap(spec.getPrecondition());
    post = postWrapper.wrap(spec.getPostcondition());
    // TODO: Assignable.
  }

  /** {@inheritDoc} */
  public void accept(final MethodSpecVisitor v) {
    v.visitPrecondition(pre);
    v.visitPostcondition(post);
    // TODO: Assignable.
  }
}
