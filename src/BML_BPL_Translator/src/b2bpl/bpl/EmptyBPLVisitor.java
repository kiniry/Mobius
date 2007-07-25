package b2bpl.bpl;

import b2bpl.bpl.ast.BPLArrayExpression;
import b2bpl.bpl.ast.BPLArrayType;
import b2bpl.bpl.ast.BPLAssertCommand;
import b2bpl.bpl.ast.BPLAssignmentCommand;
import b2bpl.bpl.ast.BPLAssumeCommand;
import b2bpl.bpl.ast.BPLAxiom;
import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.bpl.ast.BPLBinaryArithmeticExpression;
import b2bpl.bpl.ast.BPLBinaryLogicalExpression;
import b2bpl.bpl.ast.BPLBoolLiteral;
import b2bpl.bpl.ast.BPLBuiltInType;
import b2bpl.bpl.ast.BPLCallCommand;
import b2bpl.bpl.ast.BPLCastExpression;
import b2bpl.bpl.ast.BPLConstantDeclaration;
import b2bpl.bpl.ast.BPLEnsuresClause;
import b2bpl.bpl.ast.BPLEqualityExpression;
import b2bpl.bpl.ast.BPLFunction;
import b2bpl.bpl.ast.BPLFunctionApplication;
import b2bpl.bpl.ast.BPLFunctionParameter;
import b2bpl.bpl.ast.BPLGotoCommand;
import b2bpl.bpl.ast.BPLHavocCommand;
import b2bpl.bpl.ast.BPLImplementation;
import b2bpl.bpl.ast.BPLImplementationBody;
import b2bpl.bpl.ast.BPLIntLiteral;
import b2bpl.bpl.ast.BPLLogicalNotExpression;
import b2bpl.bpl.ast.BPLModifiesClause;
import b2bpl.bpl.ast.BPLNullLiteral;
import b2bpl.bpl.ast.BPLOldExpression;
import b2bpl.bpl.ast.BPLParameterizedType;
import b2bpl.bpl.ast.BPLPartialOrderExpression;
import b2bpl.bpl.ast.BPLProcedure;
import b2bpl.bpl.ast.BPLProgram;
import b2bpl.bpl.ast.BPLQuantifierExpression;
import b2bpl.bpl.ast.BPLRelationalExpression;
import b2bpl.bpl.ast.BPLRequiresClause;
import b2bpl.bpl.ast.BPLReturnCommand;
import b2bpl.bpl.ast.BPLSpecification;
import b2bpl.bpl.ast.BPLTrigger;
import b2bpl.bpl.ast.BPLTypeDeclaration;
import b2bpl.bpl.ast.BPLTypeName;
import b2bpl.bpl.ast.BPLUnaryMinusExpression;
import b2bpl.bpl.ast.BPLVariable;
import b2bpl.bpl.ast.BPLVariableDeclaration;
import b2bpl.bpl.ast.BPLVariableExpression;


public class EmptyBPLVisitor<R> implements IBPLVisitor<R> {

  public R visitProgram(BPLProgram program) {
    // do nothing
    return null;
  }

  public R visitAxiom(BPLAxiom axiom) {
    // do nothing
    return null;
  }

  public R visitConstantDeclaration(BPLConstantDeclaration declaration) {
    // do nothing
    return null;
  }

  public R visitImplementation(BPLImplementation implementation) {
    // do nothing
    return null;
  }

  public R visitProcedure(BPLProcedure procedure) {
    // do nothing
    return null;
  }

  public R visitTypeDeclaration(BPLTypeDeclaration declaration) {
    // do nothing
    return null;
  }

  public R visitVariableDeclaration(BPLVariableDeclaration declaration) {
    // do nothing
    return null;
  }

  public R visitVariable(BPLVariable variable) {
    // do nothing
    return null;
  }

  public R visitFunction(BPLFunction function) {
    // do nothing
    return null;
  }

  public R visitFunctionParameter(BPLFunctionParameter parameter) {
    // do nothing
    return null;
  }

  public R visitSpecification(BPLSpecification specification) {
    // do nothing
    return null;
  }

  public R visitRequiresClause(BPLRequiresClause clause) {
    // do nothing
    return null;
  }

  public R visitModifiesClause(BPLModifiesClause clause) {
    // do nothing
    return null;
  }

  public R visitEnsuresClause(BPLEnsuresClause clause) {
    // do nothing
    return null;
  }

  public R visitImplementationBody(BPLImplementationBody body) {
    // do nothing
    return null;
  }

  public R visitBasicBlock(BPLBasicBlock block) {
    // do nothing
    return null;
  }

  public R visitAssertCommand(BPLAssertCommand command) {
    // do nothing
    return null;
  }

  public R visitAssumeCommand(BPLAssumeCommand command) {
    // do nothing
    return null;
  }

  public R visitAssignmentCommand(BPLAssignmentCommand command) {
    // do nothing
    return null;
  }

  public R visitCallCommand(BPLCallCommand command) {
    // do nothing
    return null;
  }

  public R visitHavocCommand(BPLHavocCommand command) {
    // do nothing
    return null;
  }

  public R visitGotoCommand(BPLGotoCommand command) {
    // do nothing
    return null;
  }

  public R visitReturnCommand(BPLReturnCommand command) {
    // do nothing
    return null;
  }

  public R visitArrayExpression(BPLArrayExpression expr) {
    // do nothing
    return null;
  }

  public R visitBinaryArithmeticExpression(
      BPLBinaryArithmeticExpression expr) {
    // do nothing
    return null;
  }

  public R visitBinaryLogicalExpression(BPLBinaryLogicalExpression expr) {
    // do nothing
    return null;
  }

  public R visitEqualityExpression(BPLEqualityExpression expr) {
    // do nothing
    return null;
  }

  public R visitPartialOrderExpression(BPLPartialOrderExpression expr) {
    // do nothing
    return null;
  }

  public R visitRelationalExpression(BPLRelationalExpression expr) {
    // do nothing
    return null;
  }

  public R visitCastExpression(BPLCastExpression expr) {
    // do nothing
    return null;
  }

  public R visitFunctionApplication(BPLFunctionApplication expr) {
    // do nothing
    return null;
  }

  public R visitBoolLiteral(BPLBoolLiteral literal) {
    // do nothing
    return null;
  }

  public R visitIntLiteral(BPLIntLiteral literal) {
    // do nothing
    return null;
  }

  public R visitNullLiteral(BPLNullLiteral literal) {
    // do nothing
    return null;
  }

  public R visitOldExpression(BPLOldExpression expr) {
    // do nothing
    return null;
  }

  public R visitQuantifierExpression(BPLQuantifierExpression expr) {
    // do nothing
    return null;
  }

  public R visitLogicalNotExpression(BPLLogicalNotExpression expr) {
    // do nothing
    return null;
  }

  public R visitUnaryMinusExpression(BPLUnaryMinusExpression expr) {
    // do nothing
    return null;
  }

  public R visitVariableExpression(BPLVariableExpression expr) {
    // do nothing
    return null;
  }
  
  public R visitTrigger(BPLTrigger trigger) {
    // do nothing
    return null;
  }

  public R visitBuiltInType(BPLBuiltInType type) {
    // do nothing
    return null;
  }

  public R visitTypeName(BPLTypeName type) {
    // do nothing
    return null;
  }

  public R visitArrayType(BPLArrayType type) {
    // do nothing
    return null;
  }

  public R visitParameterizedType(BPLParameterizedType type) {
    // do nothing
    return null;
  }
}
