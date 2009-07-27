package mobius.cct.bmllib;

import java.io.OutputStream;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Method;

import annot.bcclass.BCClass;

import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassVisitor;
import mobius.cct.classfile.MethodVisitor;
import mobius.cct.classfile.MutableClassFile;
import mobius.cct.util.VisitorException;

/**
 * Wrapper for bmllib class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class BmlClassFile implements MutableClassFile {
  // Bmllib class instance.
  private BCClass clazz;
  
  /**
   * Constructor.
   * @param clazz Class file to be wrapped.
   */
  public BmlClassFile(final BCClass clazz) {
    this.clazz = clazz;
  }
  
  @Override
  public ClassVisitor getWriter(final OutputStream os) {
    // TODO: Implement.
    return null;
  }

  @Override
  public void visit(final ClassVisitor v) 
    throws VisitorException {

    final String name = clazz.getBCELClass().getClassName();
    v.begin(ClassName.parseInternal(name.replace('.', '/')));
    for (final Attribute attr: 
           clazz.getBCELClass().getAttributes()) {
      v.visitAttribute(new BmlAttribute(attr));
    }
    for (final Method m : 
           clazz.getBCELClass().getMethods()) {
      final BmlMethod meth = new BmlMethod(m);
      final MethodVisitor mv = v.visitMethod(meth.getName());
      meth.accept(mv);
    }
  }
}
