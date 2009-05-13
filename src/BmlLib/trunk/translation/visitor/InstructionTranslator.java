package visitor;

import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Type;

import annot.bcclass.BCAttributeMap;
import b2bpl.bytecode.IOpCodes;
import b2bpl.bytecode.InstructionFactory;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;

public class InstructionTranslator {
  private org.apache.bcel.generic.ConstantPoolGen cpg;

  private TranslatingVisitor visitor;

  private BCAttributeMap annotations;

  public InstructionTranslator(final ConstantPoolGen cpg,
                               final TranslatingVisitor visitor,
                               BCAttributeMap annotations) {
    this.visitor = visitor;
    this.cpg = cpg;
    this.annotations = annotations;
  }

  public b2bpl.bytecode.instructions.Instruction translateInvoke(
                                                                 final org.apache.bcel.generic.InvokeInstruction instruction) {
    
    JType returnType = visitor.visit(instruction.getReturnType(cpg));
    String methodName = instruction.getMethodName(cpg);
    Type[] argTypes = instruction.getArgumentTypes(cpg);
    JType[] resArgTypes = new JType[argTypes.length];
    JReferenceType owner = visitor.visit(instruction.getClassType(cpg));
    for (int i = 0; i < argTypes.length; i++) {
      resArgTypes[i] = visitor.visit(argTypes[i]);
    }
    System.out.println(instruction.getOpcode() + "|" + owner +"|"+methodName  + "|" + returnType + "|" + resArgTypes);
    return InstructionFactory.fromMethodInsn(instruction.getOpcode(), owner,
                                             methodName, returnType,
                                             resArgTypes);
  }

  public b2bpl.bytecode.instructions.Instruction translateBranch(
                                                                 org.apache.bcel.generic.BranchInstruction instruction) {
    return InstructionFactory.fromJumpInsn(instruction.getOpcode(), visitor
        .visit(instruction.getTarget().getInstruction(), annotations
            .getAllAt(instruction.getTarget()), annotations));
  }

  public b2bpl.bytecode.instructions.Instruction translateField(
                                                                org.apache.bcel.generic.FieldInstruction instruction) {
    return InstructionFactory.fromFieldInsn(instruction.getOpcode(),
                                            (JClassType) visitor
                                                .visit(instruction
                                                    .getClassType(cpg)),
                                            instruction.getFieldName(cpg),
                                            visitor.visit(instruction
                                                .getFieldType(cpg)));
  }

  public b2bpl.bytecode.instructions.Instruction translateIinc(
                                                               org.apache.bcel.generic.IINC instruction) {
    return InstructionFactory.fromIincInsn(instruction.getIndex(), instruction
        .getIncrement());
  }

  public b2bpl.bytecode.instructions.Instruction translate(
                                                           final org.apache.bcel.generic.Instruction instruction) {
    if (instruction instanceof org.apache.bcel.generic.InvokeInstruction)
      return translateInvoke((org.apache.bcel.generic.InvokeInstruction) instruction);
    if (instruction instanceof org.apache.bcel.generic.BranchInstruction)
      return translateBranch((org.apache.bcel.generic.BranchInstruction) instruction);
    if (instruction instanceof org.apache.bcel.generic.FieldInstruction)
      return translateField((org.apache.bcel.generic.FieldInstruction) instruction);
    switch (instruction.getOpcode()) {
    case IOpCodes.ALOAD_0:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ALOAD, 0);
    case IOpCodes.ALOAD_1:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ALOAD, 1);
    case IOpCodes.ALOAD_2:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ALOAD, 2);
    case IOpCodes.ALOAD_3:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ALOAD, 3);
    case IOpCodes.ISTORE_0:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ISTORE, 0);
    case IOpCodes.ISTORE_1:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ISTORE, 1);
    case IOpCodes.ISTORE_2:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ISTORE, 2);
    case IOpCodes.ISTORE_3:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ISTORE, 3);
    case IOpCodes.ILOAD_0:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ILOAD, 0);
    case IOpCodes.ILOAD_1:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ILOAD, 1);
    case IOpCodes.ILOAD_2:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ILOAD, 2);
    case IOpCodes.ILOAD_3:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ILOAD, 3);
    case IOpCodes.ASTORE_0:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ASTORE, 0);
    case IOpCodes.ASTORE_1:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ASTORE, 1);
    case IOpCodes.ASTORE_2:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ASTORE, 2);
    case IOpCodes.ASTORE_3:
      return b2bpl.bytecode.InstructionFactory.fromVarInsn(IOpCodes.ASTORE, 3);

    case IOpCodes.IINC:
      return translateIinc((org.apache.bcel.generic.IINC) instruction);

    }
    return b2bpl.bytecode.InstructionFactory.fromInsn(instruction.getOpcode());

  }
}
