package b2bpl.bytecode;

import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.MethodVisitor;


public interface ISpecificationProvider {

  ClassVisitor forClass(JClassType type, ClassVisitor classVisitor);

  FieldVisitor forField(BCField field, FieldVisitor fieldVisitor);

  MethodVisitor forMethod(BCMethod method, MethodVisitor methodVisitor);
}
