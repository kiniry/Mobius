package mobius.bmlvcgen.vcgen;

import java.util.EnumSet;

import org.apache.bcel.generic.ObjectType;

import mobius.bmlvcgen.bml.ClassVisitor;
import mobius.bmlvcgen.bml.Field;
import mobius.bmlvcgen.bml.InvExprVisitor;
import mobius.bmlvcgen.bml.Method;
import mobius.bmlvcgen.bml.ClassFile.AccessFlag;
import mobius.bmlvcgen.bml.ClassFile.Visibility;
import mobius.bmlvcgen.main.Env;
import mobius.bmlvcgen.util.Visitable;
import mobius.directVCGen.formula.Lookup;

/**
 * A class visitor which computes
 * proof obligations (stored in Lookup).
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class VCClassVisitor implements ClassVisitor {
  //private final Logger logger;
  private final Lookup lookup;
  private final VCMethodVisitor methodVisitor;
  
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
    //logger = env.getLoggerFactory().getLogger(this.getClass());
    this.lookup = lookup;
    methodVisitor = new VCMethodVisitor(env, this.lookup, self);
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitVersion(final int major, final int minor) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitFlags(final EnumSet<AccessFlag> flags) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitName(final String name) {
    // Do nothing.
  }

  /** {@inheritDoc} */
  @Override
  public void visitSuperName(final String name) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void beginInterfaces() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitInterface(final String name) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void endInterfaces() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void beginFields() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitField(final Field field) {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void endFields() {
    // Do nothing.
  }  
  
  /** {@inheritDoc} */
  @Override
  public void beginMethods() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitMethod(final Method method) {
    method.accept(methodVisitor);
  }
  
  /** {@inheritDoc} */
  @Override
  public void endMethods() {
    // Do nothing.
  }
 
  /** {@inheritDoc} */
  @Override
  public void beginInvariants() {
    // Do nothing.
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitInvariant(
      final Visibility visibility,
      final Visitable<? super InvExprVisitor> inv) {
    // TODO:
  }
  
  /** {@inheritDoc} */
  @Override
  public void endInvariants() {
    // Do nothing.
  }
  
}
