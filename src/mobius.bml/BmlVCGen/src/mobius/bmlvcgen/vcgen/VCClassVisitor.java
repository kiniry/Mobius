package mobius.bmlvcgen.vcgen;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.ClassVisitor;
import mobius.bmlvcgen.bml.Field;
import mobius.bmlvcgen.bml.InvExprVisitor;
import mobius.bmlvcgen.bml.Method;
import mobius.bmlvcgen.bml.ClassFile.AccessFlag;
import mobius.bmlvcgen.bml.ClassFile.Visibility;
import mobius.bmlvcgen.finder.DefaultClassFinder;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.main.Env;
import mobius.bmlvcgen.util.Visitable;
import mobius.bmlvcgen.vcgen.exceptions.TranslationException;
import mobius.directvcgen.formula.Logic;
import mobius.directvcgen.formula.Lookup;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.Term;

/**
 * A class visitor which computes
 * proof obligations (stored in Lookup).
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class VCClassVisitor implements ClassVisitor {
  private final Logger logger;
  private final Lookup lookup;
  private final VCMethodVisitor methodVisitor;
  private final InvExprTranslator invTranslator;
  private boolean hasInvariants;
  // BCEL class handle
  private final JavaClass jc;
  
  /**
   * Constructor.
   * @param env Environment.
   * @param lookup Lookup object which will be filled
   *               with translated statements.
   * @param self Type of visited class.
   */
  public VCClassVisitor(final Env env, 
                        final Lookup lookup,
                        final ObjectType self) {
    logger = env.getLoggerFactory().getLogger(this.getClass());
    this.lookup = lookup;
    invTranslator = new InvExprTranslator(self);
    methodVisitor = new VCMethodVisitor(env, this.lookup, self);
    hasInvariants = false;
    // UGLY hack 
    if (env.getClassFinder() instanceof DefaultClassFinder) {
      try {
        jc = ((DefaultClassFinder)env.getClassFinder())
               .getRepo().loadClass(self.getClassName());
      } catch (final ClassNotFoundException e) {
        logger.error("Ugly hack doesn't work." +
                     " Please rewrite the code.");
        throw new TranslationException(e);
      }
    } else {
      logger.error("Ugly hack doesn't work. " + 
                   "Please rewrite the code.");
      throw new TranslationException("UGLY HACK");
    }
  }
  
  /** {@inheritDoc} */
  public void visitVersion(final int major, final int minor) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void visitFlags(final EnumSet<AccessFlag> flags) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void visitName(final String name) {
    // Do nothing.
  }

  /** {@inheritDoc} */
  public void visitSuperName(final String name) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void beginInterfaces() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void visitInterface(final String name) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void endInterfaces() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void beginFields() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void visitField(final Field field) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void endFields() {
    // Do nothing.
  }  
  
  /** {@inheritDoc} */
  public void beginMethods() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void visitMethod(final Method method) {
    method.accept(methodVisitor);
  }
  
  /** {@inheritDoc} */
  public void endMethods() {
    // Do nothing.
  }
 
  /** {@inheritDoc} */
  public void beginInvariants() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  public void visitInvariant(
      final Visibility visibility,
      final Visitable<? super InvExprVisitor> inv) {
    hasInvariants = true;
    inv.accept(invTranslator);
    final Term t = invTranslator.getLastExpr();
    lookup.addInvariant(jc, Logic.boolToPred(t));
  }
  
  /** {@inheritDoc} */
  public void endInvariants() {
    // Create a default invariant if necessary. 
    if (!hasInvariants) {
      lookup.addInvariant(jc, Logic.boolToPred(Logic.trueValue()));
    }
  }
  
}
