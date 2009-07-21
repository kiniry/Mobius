package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.bml.MethodNameVisitor;

import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

/**
 * Wrapper for BCEL method name and type info.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class BmllibMethodName implements MethodName {
  // Wrapped method name.
  private final MethodGen method;
  
  /**
   * Constructor.
   * @param method BCEL method name.
   */
  protected BmllibMethodName(final MethodGen method) {
    this.method = method;
  }
  
  /**
   * Create instance.
   * @param method BCEL method name.
   * @return Instance.
   */
  public static BmllibMethodName getInstance(
                                    final MethodGen method) {
    // TODO: Cache
    return new BmllibMethodName(method);
  }
  
  /** {@inheritDoc} */
  public void accept(final MethodNameVisitor v) {
    v.visitName(method.getName());
    v.visitResultType(
      BcelResultType.getInstance(method.getReturnType()));
    v.beginArgs();
    int i = 0;
    for (final Type t : method.getArgumentTypes()) {
      v.visitArg(BcelType.getInstance(t), 
                 method.getArgumentName(i++));
    }
    v.endArgs();
  }

  /**
   * Get wrapped method.
   * @return Wrapped method.
   */
  public MethodGen getMethodGen() {
    return method;
  }
  
}
