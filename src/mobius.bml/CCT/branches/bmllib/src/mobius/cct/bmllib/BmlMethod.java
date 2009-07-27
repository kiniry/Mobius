package mobius.cct.bmllib;

import java.io.IOException;

import mobius.cct.classfile.MethodName;
import mobius.cct.classfile.MethodType;
import mobius.cct.classfile.MethodVisitor;
import mobius.cct.util.VisitorException;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Method;

/**
 * Wrapper for BCEL methods.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class BmlMethod {
  // Wrapped method.
  private final Method method;
  
  /**
   * Constructor.
   * @param method Method to be wrapped.
   */
  public BmlMethod(final Method method) {
    this.method = method;
  }
  
  /**
   * Visit this method.
   * @param v Visitor.
   * @throws VisitorException .
   */
  public void accept(final MethodVisitor v) 
    throws VisitorException {
    
    if (v == null) { return; }
    v.begin(getName());
    for (final Attribute attr : method.getAttributes()) {
      v.visitAttribute(new BmlAttribute(attr));
    }
    v.end();
  }
  
  /**
   * Get name and type of this method.
   * @param method Method.
   * @return Name and type.
   */
  public MethodName getName() {
    final MethodType type;
    try {
      type = MethodType.parse(method.getSignature());
    } catch (final IOException e) {
      return null; // :-(
    }
    final MethodName name = 
      new MethodName(method.getName(), type);
    return name;
  }
}
