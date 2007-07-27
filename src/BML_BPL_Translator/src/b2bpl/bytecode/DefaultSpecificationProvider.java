package b2bpl.bytecode;

import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.MethodVisitor;

import b2bpl.bytecode.attributes.MethodSpecificationAttribute;
import b2bpl.bytecode.bml.ast.BMLBooleanLiteral;
import b2bpl.bytecode.bml.ast.BMLEnsuresClause;
import b2bpl.bytecode.bml.ast.BMLExsuresClause;
import b2bpl.bytecode.bml.ast.BMLMethodSpecification;
import b2bpl.bytecode.bml.ast.BMLModifiesClause;
import b2bpl.bytecode.bml.ast.BMLNothingStoreRef;
import b2bpl.bytecode.bml.ast.BMLPredicate;
import b2bpl.bytecode.bml.ast.BMLRequiresClause;
import b2bpl.bytecode.bml.ast.BMLSpecificationCase;


public class DefaultSpecificationProvider implements ISpecificationProvider {

  public ClassVisitor forClass(JClassType type, ClassVisitor classVisitor) {
    return classVisitor;
  }

  public FieldVisitor forField(BCField field, FieldVisitor fieldVisitor) {
    return fieldVisitor;
  }

  public MethodVisitor forMethod(BCMethod method, MethodVisitor methodVisitor) {
    if ((methodVisitor != null)
        && method.isConstructor()
        && method.getOwner().getName().equals("java.lang.Object")
        && (method.getParameterCount() == 0)) {
      BMLSpecificationCase specCase = new BMLSpecificationCase(
          new BMLRequiresClause(new BMLPredicate(BMLBooleanLiteral.TRUE)),
          new BMLModifiesClause(BMLNothingStoreRef.NOTHING),
          new BMLEnsuresClause(new BMLPredicate(BMLBooleanLiteral.TRUE)),
          BMLExsuresClause.EMPTY_ARRAY);
      BMLMethodSpecification spec = new BMLMethodSpecification(
          new BMLRequiresClause(new BMLPredicate(BMLBooleanLiteral.TRUE)),
          specCase);
      methodVisitor.visitAttribute(new MethodSpecificationAttribute(spec));
    }
    return methodVisitor;
  }
}
