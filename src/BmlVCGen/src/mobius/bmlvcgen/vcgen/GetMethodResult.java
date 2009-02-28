package mobius.bmlvcgen.vcgen;

import mobius.bmlvcgen.bml.MethodNameVisitor;
import mobius.bmlvcgen.bml.types.ResultType;
import mobius.bmlvcgen.bml.types.Type;

/**
 * Simple visitor which can extract return type
 * of a method.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class GetMethodResult implements MethodNameVisitor {
  private ResultType resultType;

  /** {@inheritDoc} */
  @Override
  public void beginArgs() {
  }

  /** {@inheritDoc} */
  @Override
  public void endArgs() {
  }

  /** {@inheritDoc} */
  @Override
  public void visitArg(final Type t, final String name) {
  }

  /** {@inheritDoc} */
  @Override
  public void visitName(final String name) {
  }

  /** {@inheritDoc} */
  @Override
  public void visitResultType(final ResultType t) {
    resultType = t;
  }
  
  /**
   * Get result type of last method visited.
   * @return Result type.
   */
  public ResultType getType() {
    return resultType;
  }
}
