package visitor;

import java.util.Vector;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

import annot.bcclass.BCClass;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.ast.BMLConstraint;
import b2bpl.bytecode.bml.ast.BMLInvariant;

public class TranslatingVisitor {
  private ConstantPoolGen cpg;
  public JClassType visit(BCClass clazz) {
    cpg = new ConstantPoolGen(clazz.getJC().getConstantPool());
    final JClassType type = new JClassType(clazz.getJC().getClassName());
    b2bpl.bytecode.BCMethod[] resMethods = new b2bpl.bytecode.BCMethod[clazz.getMethodCount()];
    for (int i = 0; i < clazz.getMethodCount(); i++) {
    
      resMethods[i] = visit(clazz.getMethod(i), type);
    }
    type.setDeclarations(new BCField[0], resMethods, new BMLInvariant[0], new BMLConstraint[0]);
    return type;
  }

  public b2bpl.bytecode.BCMethod visit(annot.bcclass.BCMethod method,
                                       JClassType owner) {
    MethodGen bcm = method.getBcelMethod();
    JType returnType = visit(bcm.getReturnType());
    int len = bcm.getArgumentTypes().length;
    JType[] paramTypes = new JType[len];
    for (int i = 0; i < len; i++) {
      paramTypes[i] = visit(bcm.getArgumentType(i));
    }
    int excLen = bcm.getExceptions().length;
    JClassType[] exc = new JClassType[excLen];
    for (int i = 0; i < excLen; i++) {
      exc[i] = new JClassType(bcm.getExceptions()[i]);
    }
    b2bpl.bytecode.BCMethod resMethod = new b2bpl.bytecode.BCMethod(bcm
        .getAccessFlags(), owner, bcm.getName(), returnType, paramTypes, exc);
    InstructionList instructions = bcm.getInstructionList();
    final b2bpl.bytecode.Instructions retInstr = new b2bpl.bytecode.Instructions();
    if (instructions != null) {
      final org.apache.bcel.generic.InstructionHandle[] origInstr = instructions
          .getInstructionHandles();
      for (int i = 0; i < origInstr.length; i++) {
        
        retInstr.add(visit(origInstr[i].getInstruction()));
      }
    }
    resMethod.setSpecification(visit(method.getMspec()));
    return resMethod;
  }
  public b2bpl.bytecode.bml.ast.BMLMethodSpecification visit(annot.attributes.MethodSpecification spec){
   Vector<annot.attributes.SpecificationCase> cases = spec.getSpecificationCases();
   for (annot.attributes.SpecificationCase specCase :cases){
     specCase.
   }
   
   return null;
  }
  public b2bpl.bytecode.InstructionHandle visit(
                                                final org.apache.bcel.generic.Instruction instruction) {
    final b2bpl.bytecode.InstructionHandle res = new b2bpl.bytecode.InstructionHandle();
    InstructionTranslator translator = new InstructionTranslator(cpg, this);
    res.setInstruction(translator.translate(instruction));
    
    

    return res;
  }
  
  public JArrayType visit (ArrayType type) {
    return new JArrayType(visit(type.getElementType()), type.getDimensions()); 
  } 
  public JType visit(Type type) {
    return JType.fromDescriptor(type.getSignature());
  }
  public JReferenceType visit(ObjectType type){
    return null;
  }
}
