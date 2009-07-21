package b2bpl.bytecode.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.analysis.AnalyzerException;

import b2bpl.Project;
import b2bpl.bytecode.B2BPLMessages;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.BCMethod;
import b2bpl.bytecode.EmptyInstructionVisitor;
import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.JBaseType;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JNullType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.TroubleMessage;
import b2bpl.bytecode.TroublePosition;
import b2bpl.bytecode.ITroubleReporter;
import b2bpl.bytecode.TypeLoader;
import b2bpl.bytecode.bml.IBMLExpressionVisitor;
import b2bpl.bytecode.bml.IBMLStoreRefVisitor;
import b2bpl.bytecode.bml.ast.BMLArrayAccessExpression;
import b2bpl.bytecode.bml.ast.BMLArrayAllStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayElementStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayLengthExpression;
import b2bpl.bytecode.bml.ast.BMLArrayRangeStoreRef;
import b2bpl.bytecode.bml.ast.BMLAssertStatement;
import b2bpl.bytecode.bml.ast.BMLAssumeStatement;
import b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryBitwiseExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryLogicalExpression;
import b2bpl.bytecode.bml.ast.BMLBooleanLiteral;
import b2bpl.bytecode.bml.ast.BMLBoundVariableExpression;
import b2bpl.bytecode.bml.ast.BMLCastExpression;
import b2bpl.bytecode.bml.ast.BMLConstraint;
import b2bpl.bytecode.bml.ast.BMLElemTypeExpression;
import b2bpl.bytecode.bml.ast.BMLEqualityExpression;
import b2bpl.bytecode.bml.ast.BMLEverythingStoreRef;
import b2bpl.bytecode.bml.ast.BMLExpression;
import b2bpl.bytecode.bml.ast.BMLExsuresClause;
import b2bpl.bytecode.bml.ast.BMLFieldAccessExpression;
import b2bpl.bytecode.bml.ast.BMLFieldAccessStoreRef;
import b2bpl.bytecode.bml.ast.BMLFieldExpression;
import b2bpl.bytecode.bml.ast.BMLFieldStoreRef;
import b2bpl.bytecode.bml.ast.BMLFreshExpression;
import b2bpl.bytecode.bml.ast.BMLInstanceOfExpression;
import b2bpl.bytecode.bml.ast.BMLIntLiteral;
import b2bpl.bytecode.bml.ast.BMLInvariant;
import b2bpl.bytecode.bml.ast.BMLLocalVariableExpression;
import b2bpl.bytecode.bml.ast.BMLLocalVariableStoreRef;
import b2bpl.bytecode.bml.ast.BMLLogicalNotExpression;
import b2bpl.bytecode.bml.ast.BMLLoopSpecification;
import b2bpl.bytecode.bml.ast.BMLMethodSpecification;
import b2bpl.bytecode.bml.ast.BMLNothingStoreRef;
import b2bpl.bytecode.bml.ast.BMLNullLiteral;
import b2bpl.bytecode.bml.ast.BMLOldExpression;
import b2bpl.bytecode.bml.ast.BMLPredicate;
import b2bpl.bytecode.bml.ast.BMLQuantifierExpression;
import b2bpl.bytecode.bml.ast.BMLRelationalExpression;
import b2bpl.bytecode.bml.ast.BMLResultExpression;
import b2bpl.bytecode.bml.ast.BMLSpecificationCase;
import b2bpl.bytecode.bml.ast.BMLStackCounterExpression;
import b2bpl.bytecode.bml.ast.BMLStackElementExpression;
import b2bpl.bytecode.bml.ast.BMLStoreRef;
import b2bpl.bytecode.bml.ast.BMLThisExpression;
import b2bpl.bytecode.bml.ast.BMLThisStoreRef;
import b2bpl.bytecode.bml.ast.BMLTypeOfExpression;
import b2bpl.bytecode.bml.ast.BMLUnaryMinusExpression;
import b2bpl.bytecode.instructions.GetFieldInstruction;
import b2bpl.bytecode.instructions.GetStaticInstruction;
import b2bpl.bytecode.instructions.InvokeInterfaceInstruction;
import b2bpl.bytecode.instructions.InvokeSpecialInstruction;
import b2bpl.bytecode.instructions.InvokeStaticInstruction;
import b2bpl.bytecode.instructions.InvokeVirtualInstruction;
import b2bpl.bytecode.instructions.PutFieldInstruction;
import b2bpl.bytecode.instructions.PutStaticInstruction;


public class SemanticAnalyzer {

  private final Project project;

  private final ITroubleReporter troubleReporter;

  private HashMap<String, MethodNode> asmMethods = new HashMap<String, MethodNode>();

  public SemanticAnalyzer(Project project, ITroubleReporter troubleReporter) {
    this.project = project;
    this.troubleReporter = troubleReporter;
  }

  public void analyze(JClassType... types) {
    for (JClassType type : types) {
      analyzeInterface(type);
      analyzeMethodBodies(type);
    }
  }

  private void analyzeInterface(JClassType type) {
    analyzeTypeSpecifications(type);
    analyzeMethodSpecifications(type);
  }

  private void analyzeTypeSpecifications(JClassType type) {
    BMLAnalyzer bmlAnalyzer = new BMLAnalyzer(type);
    for (BMLInvariant invariant : type.getInvariants()) {
      invariant.getPredicate().accept(bmlAnalyzer);
    }
    for (BMLConstraint constraint : type.getConstraints()) {
      constraint.getPredicate().accept(bmlAnalyzer);
    }
  }

  private void analyzeMethodSpecifications(JClassType type) {
    for (BCMethod method : type.getMethods()) {
      BMLAnalyzer bmlAnalyzer = new BMLAnalyzer(method);
      BMLMethodSpecification spec = method.getSpecification();
      if (spec != null) {
        spec.getRequires().getPredicate().accept(bmlAnalyzer);
        for (BMLSpecificationCase specCase : spec.getCases()) {
          specCase.getRequires().getPredicate().accept(bmlAnalyzer);
          for (BMLStoreRef storeRef : specCase.getModifies().getStoreRefs()) {
            storeRef.accept(bmlAnalyzer);
          }
          specCase.getEnsures().getPredicate().accept(bmlAnalyzer);
          for (BMLExsuresClause exsure : specCase.getExsures()) {
            BMLAnalyzer exBMLAnalyzer =
              new BMLAnalyzer(method, exsure.getExceptionType());
            exsure.getPredicate().accept(exBMLAnalyzer);
          }
        }
      }
    }
  }

  private MethodNode getASMMethod(BCMethod method) {
    String key = method.getQualifiedName() + method.getDescriptor();
    if (asmMethods.get(key) == null) {
      ClassNode cn = TypeLoader.getASMClassTypeNode(method.getOwner());
      for (Object o : cn.methods) {
        MethodNode mn = (MethodNode) o;
        asmMethods.put(cn.name.replace('/', '.') + "." + mn.name + mn.desc, mn);
      }
    }
    return asmMethods.get(key);
  }

  private void analyzeMethodBodies(JClassType type) {
    InstructionAnalyzer insnAnalyzer = new InstructionAnalyzer();
    CFGBuilder cfgBuilder = new CFGBuilder(project.isModelRuntimeExceptions());
    
    FlowAnalyzer flowAnalyzer = new FlowAnalyzer(project.isModelRuntimeExceptions());
   
    for (BCMethod method : type.getMethods()) {
      try {
        if (method.getInstructions() != null) {
          
          method.getInstructions().accept(insnAnalyzer);
          
          flowAnalyzer.analyze(type.getInternalName(), getASMMethod(method));
          ControlFlowGraph cfg = cfgBuilder.build(method);
          cfg.analyze();
          method.setCFG(cfg);
          if (!cfg.isReducible()) {
            troubleReporter.reportTrouble(
                new TroubleMessage(
                    new TroublePosition(method, null),
                    B2BPLMessages.IRREDUCIBLE_CONTROL_FLOW_GRAPH));
          }
          analyzeInstructionSpecifications(method);
        }
      } catch (AnalyzerException e) {
        troubleReporter.reportTrouble(
            new TroubleMessage(
                new TroublePosition(method, null),
                B2BPLMessages.ERROR_DURING_DATAFLOW_ANALYSIS,
                e.getMessage()));
      }
    }
  }

  private static void analyzeInstructionSpecifications(BCMethod method) {
    for (InstructionHandle insn : method.getInstructions()) {
      BMLAnalyzer bmlAnalyzer = new BMLAnalyzer(method, insn);
      for (BMLAssertStatement assertion : insn.getAssertions()) {
        assertion.getPredicate().accept(bmlAnalyzer);
      }
      for (BMLAssumeStatement assumption : insn.getAssumptions()) {
        assumption.getPredicate().accept(bmlAnalyzer);
      }
      for (BMLLoopSpecification loopSpec : insn.getLoopSpecifications()) {
        loopSpec.getInvariant().getPredicate().accept(bmlAnalyzer);
        for (BMLStoreRef storeRef : loopSpec.getModifies().getStoreRefs()) {
          storeRef.accept(bmlAnalyzer);
        }
        loopSpec.getVariant().getExpression().accept(bmlAnalyzer);
      }
    }
  }

  private static final class InstructionAnalyzer
      extends EmptyInstructionVisitor {

    public void visitGetFieldInstruction(GetFieldInstruction insn) {
      // REVIEW[om]: Check for correct lookup!
      insn.setField(insn.getFieldOwner().lookupField(insn.getFieldName()));
    }

    public void visitPutFieldInstruction(PutFieldInstruction insn) {
      // REVIEW[om]: Check for correct lookup!
      insn.setField(insn.getFieldOwner().lookupField(insn.getFieldName()));
    }

    public void visitGetStaticInstruction(GetStaticInstruction insn) {
      // REVIEW[om]: Check for correct lookup!
      insn.setField(insn.getFieldOwner().lookupField(insn.getFieldName()));
    }

    public void visitPutStaticInstruction(PutStaticInstruction insn) {
      // REVIEW[om]: Check for correct lookup!
      insn.setField(insn.getFieldOwner().lookupField(insn.getFieldName()));
    }

    public void visitInvokeVirtualInstruction(InvokeVirtualInstruction insn) {
      // REVIEW[om]: Check for correct lookup!
      String name = insn.getMethodName();
      String desc = insn.getMethodDescriptor();
      insn.setMethod(insn.getMethodOwner().lookupMethod(name, desc));
    }

    public void visitInvokeStaticInstruction(InvokeStaticInstruction insn) {
      // REVIEW[om]: Check for correct lookup!
      String name = insn.getMethodName();
      String desc = insn.getMethodDescriptor();
      insn.setMethod(insn.getMethodOwner().lookupMethod(name, desc));
    }

    public void visitInvokeSpecialInstruction(InvokeSpecialInstruction insn) {
      // REVIEW[om]: Check for correct lookup!
      String name = insn.getMethodName();
      String desc = insn.getMethodDescriptor();
      insn.setMethod(insn.getMethodOwner().lookupMethod(name, desc));
    }

    public void visitInvokeInterfaceInstruction(
        InvokeInterfaceInstruction insn) {
      // REVIEW[om]: Check for correct lookup!
      String name = insn.getMethodName();
      String desc = insn.getMethodDescriptor();
      insn.setMethod(insn.getMethodOwner().lookupMethod(name, desc));
    }
  }

  private static final class BMLAnalyzer
      implements IBMLExpressionVisitor<Object>, IBMLStoreRefVisitor<Object> {

    private final JClassType type;

    private final BCMethod method;

    private final InstructionHandle instruction;

    private final List<JType> boundVariableTypes = new ArrayList<JType>();

    public BMLAnalyzer(JClassType type) {
      this.type = type;
      this.method = null;
      this.instruction = null;
    }

    public BMLAnalyzer(BCMethod method) {
      this.type = method.getOwner();
      this.method = method;
      this.instruction = null;
    }

    public BMLAnalyzer(BCMethod method, JType exception) {
      this.type = method.getOwner();
      this.method = method;
      this.instruction = null;
      this.boundVariableTypes.add(exception);
    }

    public BMLAnalyzer(BCMethod method, InstructionHandle instruction) {
      this.type = method.getOwner();
      this.method = method;
      this.instruction = instruction;
    }

    private JType getLocalVariableType(int index) {
      if (instruction != null) {
        return instruction.getFrame().getLocal(index);
      }
      return method.getRealParameterTypes()[index];
    }

    private JType getStackElementType(int index) {
      return instruction.getFrame().peek(index);
    }

    private int getStackSize() {
      return instruction.getFrame().getStackSize();
    }

    private JType getBoundVariableType(int index) {
      return boundVariableTypes.get(index);
    }

    private void addBoundVariableTypes(JType... types) {
      for (int i = 0; i < types.length; i++) {
        boundVariableTypes.add(i, types[i]);
      }
    }

    private void removeBoundVariableTypes(int count) {
      for (int i = 0; i < count; i++) {
        boundVariableTypes.remove(0);
      }
    }

    public Object visitQuantifierExpression(BMLQuantifierExpression expr) {
      addBoundVariableTypes(expr.getVariableTypes());
      expr.getExpression().accept(this);
      removeBoundVariableTypes(expr.getVariableTypes().length);
      expr.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitBinaryArithmeticExpression(
        BMLBinaryArithmeticExpression expr) {
      expr.getLeft().accept(this);
      expr.getRight().accept(this);
      expr.setType(JBaseType.INT);
      return null;
    }

    public Object visitBinaryLogicalExpression(
        BMLBinaryLogicalExpression expr) {
      expr.getLeft().accept(this);
      expr.getRight().accept(this);
      expr.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitEqualityExpression(BMLEqualityExpression expr) {
      expr.getLeft().accept(this);
      expr.getRight().accept(this);
      expr.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitRelationalExpression(BMLRelationalExpression expr) {
      expr.getLeft().accept(this);
      expr.getRight().accept(this);
      expr.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitBinaryBitwiseExpression(BMLBinaryBitwiseExpression expr) {
      expr.getLeft().accept(this);
      expr.getRight().accept(this);
      expr.setType(JBaseType.INT);
      return null;
    }

    public Object visitUnaryMinusExpression(BMLUnaryMinusExpression expr) {
      expr.getExpression().accept(this);
      expr.setType(JBaseType.INT);
      return null;
    }

    public Object visitLogicalNotExpression(BMLLogicalNotExpression expr) {
      expr.getExpression().accept(this);
      expr.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitInstanceOfExpression(BMLInstanceOfExpression expr) {
      expr.getExpression().accept(this);
      expr.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitCastExpression(BMLCastExpression expr) {
      expr.getExpression().accept(this);
      expr.setType(expr.getTargetType());
      return null;
    }

    public Object visitBooleanLiteral(BMLBooleanLiteral literal) {
      literal.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitIntLiteral(BMLIntLiteral literal) {
      literal.setType(JBaseType.INT);
      return null;
    }

    public Object visitNullLiteral(BMLNullLiteral literal) {
      literal.setType(JNullType.NULL);
      return null;
    }

    public Object visitLocalVariableExpression(
        BMLLocalVariableExpression expr) {
      expr.setType(getLocalVariableType(expr.getIndex()));
      return null;
    }

    public Object visitBoundVariableExpression(
        BMLBoundVariableExpression expr) {
      expr.setType(getBoundVariableType(expr.getIndex()));
      return null;
    }

    public Object visitStackElementExpression(BMLStackElementExpression expr) {
      expr.getIndexExpression().accept(this);
      // REVIEW[om]: Make this nicer.
      BMLExpression idxExpr = expr.getIndexExpression();
      if (idxExpr instanceof BMLIntLiteral) {
        expr.setIndex(((BMLIntLiteral) idxExpr).getValue());
      }
      expr.setType(getStackElementType(expr.getIndex()));
      return null;
    }

    public Object visitStackCounterExpression(BMLStackCounterExpression expr) {
      expr.setCounter(getStackSize());
      expr.setType(JBaseType.INT);
      return null;
    }

    public Object visitOldExpression(BMLOldExpression expr) {
      expr.getExpression().accept(this);
      expr.setType(expr.getExpression().getType());
      return null;
    }

    public Object visitPredicate(BMLPredicate predicate) {
      predicate.getExpression().accept(this);
      predicate.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitFieldExpression(BMLFieldExpression expr) {
      // REVIEW[om]: Check for correct lookup!
      BCField field = expr.getFieldOwner().lookupField(expr.getFieldName());
      expr.setField(field);
      expr.setType(field.getType());
      return null;
    }

    public Object visitFieldAccessExpression(BMLFieldAccessExpression expr) {
      expr.getPrefix().accept(this);
      expr.getFieldReference().accept(this);
      expr.setType(expr.getFieldReference().getType());
      return null;
    }

    public Object visitArrayAccessExpression(BMLArrayAccessExpression expr) {
      expr.getPrefix().accept(this);
      expr.getIndex().accept(this);
      JArrayType arrayType = (JArrayType) expr.getPrefix().getType();
      expr.setType(arrayType.getIndexedType());
      return null;
    }

    public Object visitArrayLengthExpression(BMLArrayLengthExpression expr) {
      expr.getPrefix().accept(this);
      expr.setType(JBaseType.INT);
      return null;
    }

    public Object visitTypeOfExpression(BMLTypeOfExpression expr) {
      expr.getExpression().accept(this);
      // FIXME[OJM]: What to set as type?
      return null;
    }

    public Object visitElemTypeExpression(BMLElemTypeExpression expr) {
      expr.getTypeExpression().accept(this);
      // FIXME[OJM]: What to set as type?
      return null;
    }

    public Object visitResultExpression(BMLResultExpression expr) {
      expr.setType(method.getReturnType());
      return null;
    }

    public Object visitThisExpression(BMLThisExpression expr) {
      expr.setType(type);
      return null;
    }

    public Object visitFreshExpression(BMLFreshExpression expr) {
      expr.getExpression().accept(this);
      expr.setType(JBaseType.BOOLEAN);
      return null;
    }

    public Object visitEverythingStoreRef(BMLEverythingStoreRef storeRef) {
      return null;
    }

    public Object visitNothingStoreRef(BMLNothingStoreRef storeRef) {
      return null;
    }

    public Object visitThisStoreRef(BMLThisStoreRef storeRef) {
      return null;
    }

    public Object visitLocalVariableStoreRef(
        BMLLocalVariableStoreRef storeRef) {
      return null;
    }

    public Object visitFieldStoreRef(BMLFieldStoreRef storeRef) {
      // REVIEW[om]: Check for correct lookup!
      BCField field =
        storeRef.getFieldOwner().lookupField(storeRef.getFieldName());
      storeRef.setField(field);
      return null;
    }

    public Object visitFieldAccessStoreRef(BMLFieldAccessStoreRef storeRef) {
      storeRef.getPrefix().accept(this);
      storeRef.getField().accept(this);
      return null;
    }

    public Object visitArrayElementStoreRef(BMLArrayElementStoreRef storeRef) {
      storeRef.getPrefix().accept(this);
      storeRef.getIndex().accept(this);
      return null;
    }

    public Object visitArrayAllStoreRef(BMLArrayAllStoreRef storeRef) {
      storeRef.getPrefix().accept(this);
      return null;
    }

    public Object visitArrayRangeStoreRef(BMLArrayRangeStoreRef storeRef) {
      storeRef.getPrefix().accept(this);
      storeRef.getStartIndex().accept(this);
      storeRef.getEndIndex().accept(this);
      return null;
    }
  }
}
