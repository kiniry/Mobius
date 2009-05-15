package mobius.bmlvcgen.vcgen;

import mobius.bmlvcgen.bml.MethodSpecVisitor;
import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.main.Env;
import mobius.bmlvcgen.util.Visitable;
import mobius.bmlvcgen.vcgen.exceptions.TranslationException;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.vcgen.struct.Post;

import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * A visitor for method specifications.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class VCSpecVisitor implements MethodSpecVisitor {
  private final Logger logger;
  private final Lookup lookup;
  private final MethodGen method;
  private final QuantVariable resultVar;
  private final PreExprTranslator preTranslator;
  private final PostExprTranslator postTranslator;
  private int counter;
  
  /**
   * Constructor.
   * @param env Environment.
   * @param lookup Lookup object.
   * @param self Type of 'this' object.
   * @param method Processed method.
   * @param resultSort Sort of method result.
   */
  public VCSpecVisitor(final Env env, 
                       final Lookup lookup,
                       final ObjectType self,
                       final MethodGen method,
                       final Sort resultSort) {
    logger = env.getLoggerFactory().getLogger(this.getClass());
    this.lookup = lookup;
    this.method = method;
    resultVar = Expression.var(resultSort);
    preTranslator = new PreExprTranslator(self);
    postTranslator = new PostExprTranslator(
      self, 
      method.getReturnType(),
      resultVar);
    counter = 0;
  }

  /** {@inheritDoc} */
  @Override
  public void visitPostcondition(
      final Visitable<? super PostExprVisitor> post) {
    post.accept(postTranslator);
    final Term pterm = postTranslator.getLastExpr();
    final Post postcondition = new Post(
      Expression.rvar(resultVar),
      Logic.boolToPred(pterm)
    );
    lookup.addNormalPostcondition(method, postcondition);
  }

  /** {@inheritDoc} */
  @Override
  public void visitPrecondition(final 
      Visitable<? super PreExprVisitor> pre) {
    // TODO : HOW to specify multiple spec cases in directvcgen?!?!?
    // Is this possible?
    if (counter > 0) {
      throw new TranslationException(
        "Multiple specification cases are not supported."
      );
    }
    counter++;
    pre.accept(preTranslator);
    final Term precondition = preTranslator.getLastExpr();
    if (Logic.sort.equals(precondition.getSort())) {
      lookup.addPrecondition(method, precondition);
    } else {
      lookup.addPrecondition(method, 
                             Logic.boolToPred(precondition));
    }
  }

  /** {@inheritDoc} */
  @Override
  public void visitSignals(
               final String exc, 
               final Visitable<? super PostExprVisitor> expr) {
    // TODO: Implement.
  }
  
  /**
   * Fill lookup with fake pre and postconditions
   * if none were defined.
   */
  public void end() {
    if (counter == 0) {
      logger.debug("Adding default specification to method " + 
                   method.getName());
      lookup.addPrecondition(method, Logic.trueValue());
      lookup.addNormalPostcondition(
          method, 
          new Post(Expression.rvar(resultVar), 
                   Logic.trueValue()));
    }
  }
}
