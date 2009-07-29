package mobius.cct.bmllib;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.Map;

import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ClassGen;

import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassVisitor;
import mobius.cct.classfile.MethodName;
import mobius.cct.classfile.MethodVisitor;
import mobius.cct.util.VisitorException;

import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;

/**
 * Bmllib class writer.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class BmlWriter implements ClassVisitor {
  // Bmllib class.
  private final BCClass clazz;
  // Output stream.
  private final OutputStream os;
  // Methods.
  private final Map<MethodName, Method> methods;
  
  /**
   * Constructor.
   * @param clazz Source class.
   * @param os Output stream.
   */
  public BmlWriter(final BCClass clazz,
                   final OutputStream os) {
    BCClass bc;
    try {
      bc = new BCClass(
          ((ClassGen)clazz.getBCELClass().clone()).getJavaClass());
    } catch (final ReadAttributeException e) {
      bc = null;
      // :-(
    }
    this.clazz = bc;
    this.os = os;
    methods = new HashMap<MethodName, Method>();
    for (final Method m : clazz.getJC().getMethods()) {
      methods.put(getMethodName(m), m);
    }
  }

  private static MethodName getMethodName(final Method m) {
    return MethodName.get(m.getName(), m.getSignature());
  }
  
  /** {@inheritDoc} */
  @Override
  public void begin(final ClassName cls) 
    throws VisitorException {
    // Class name is ignored.
  }

  /** {@inheritDoc} */
  @Override
  public void end() throws VisitorException {
    System.err.println("SAVE. THIS. CLASS. TO. DISK");
    try {
      clazz.saveJC().dump(os);
    } catch (final IOException e) {
      throw new VisitorException(e);
    }
  }

  /** {@inheritDoc} */
  @Override
  public void visitAttribute(final Attribute attr) 
    throws VisitorException {
    
    final String name = attr.getName();
    final ConstantUtf8 c = new ConstantUtf8(name);
    clazz.getCp().addConstant(c, false, null);
    final int nameIndex = 
      clazz.getCp().getConstantPool().lookupUtf8(name);
    final ByteArrayOutputStream bos = 
      new ByteArrayOutputStream();
    try {
      attr.writeData(bos);
    } catch (final IOException e) {
      throw new VisitorException(e);
    }
    final ConstantPool cp = 
      clazz.getCp().getConstantPool().getConstantPool();
    final Unknown a = new Unknown(nameIndex, 
                                  bos.size(), 
                                  bos.toByteArray(),
                                  cp);
    clazz.getJC().addAttribute(a);
  }

  /** {@inheritDoc} */
  @Override
  public MethodVisitor visitMethod(final MethodName m) 
    throws VisitorException {
    return new BmlMethodWriter(clazz, methods.get(m));
  }
}
