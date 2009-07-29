package mobius.cct.bmllib;

import java.io.ByteArrayOutputStream;
import java.io.IOException;

import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.MethodGen;

import annot.bcclass.BCClass;
import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.MethodName;
import mobius.cct.classfile.MethodVisitor;
import mobius.cct.util.VisitorException;

/**
 * Class responsible for adding attributes 
 * to bmllib methods.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class BmlMethodWriter implements MethodVisitor {
  // Bmllib class.
  private final BCClass clazz;
  // BCEL method.
  private final Method method;
  // MethodGen.
  private final MethodGen methodGen;
  
  /**
   * Constructor.
   * @param clazz Class to be modified.
   * @param method Method to be modified.
   */
  public BmlMethodWriter(final BCClass clazz,
                         final Method method ) {
    this.clazz = clazz;
    this.method = method;
    this.methodGen = new MethodGen(method, 
                                clazz.getJC().getClassName(), 
                                clazz.getJC().getConstantPool());
  }
  
  /** {@inheritDoc} */
  @Override
  public void begin(final MethodName m) throws VisitorException {
    // EMPTY
  }

  /** {@inheritDoc} */
  @Override
  public void end() throws VisitorException {
    clazz.getJC().replaceMethod(method, 
                                methodGen.getMethod());
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
    methodGen.addAttribute(a);
  }
}
