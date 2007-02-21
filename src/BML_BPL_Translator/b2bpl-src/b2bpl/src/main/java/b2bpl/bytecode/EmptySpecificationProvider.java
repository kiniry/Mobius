package b2bpl.bytecode;

import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.MethodVisitor;


public class EmptySpecificationProvider implements SpecificationProvider {

  public ClassVisitor forClass(JClassType type, ClassVisitor classVisitor) {
    return classVisitor;
  }

  public FieldVisitor forField(BCField field, FieldVisitor fieldVisitor) {
    return fieldVisitor;
  }

  public MethodVisitor forMethod(BCMethod method, MethodVisitor methodVisitor) {
    return methodVisitor;
  }
}
