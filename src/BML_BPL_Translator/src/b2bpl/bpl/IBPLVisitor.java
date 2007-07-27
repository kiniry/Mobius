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


public interface IBPLVisitor<R> {

  R visitProgram(BPLProgram program);

  R visitAxiom(BPLAxiom axiom);

  R visitConstantDeclaration(BPLConstantDeclaration declaration);

  R visitImplementation(BPLImplementation implementation);

  R visitProcedure(BPLProcedure procedure);

  R visitTypeDeclaration(BPLTypeDeclaration declaration);

  R visitVariableDeclaration(BPLVariableDeclaration declaration);

  R visitVariable(BPLVariable variable);

  R visitFunction(BPLFunction function);

  R visitFunctionParameter(BPLFunctionParameter parameter);

  R visitSpecification(BPLSpecification specification);

  R visitRequiresClause(BPLRequiresClause clause);

  R visitModifiesClause(BPLModifiesClause clause);

  R visitEnsuresClause(BPLEnsuresClause clause);

  R visitImplementationBody(BPLImplementationBody body);

  R visitBasicBlock(BPLBasicBlock block);

  R visitAssertCommand(BPLAssertCommand command);

  R visitAssumeCommand(BPLAssumeCommand command);

  R visitAssignmentCommand(BPLAssignmentCommand command);

  R visitCallCommand(BPLCallCommand command);

  R visitHavocCommand(BPLHavocCommand command);

  R visitGotoCommand(BPLGotoCommand command);

  R visitReturnCommand(BPLReturnCommand command);

  R visitArrayExpression(BPLArrayExpression expr);

  R visitBinaryArithmeticExpression(BPLBinaryArithmeticExpression expr);

  R visitBinaryLogicalExpression(BPLBinaryLogicalExpression expr);

  R visitEqualityExpression(BPLEqualityExpression expr);

  R visitPartialOrderExpression(BPLPartialOrderExpression expr);

  R visitRelationalExpression(BPLRelationalExpression expr);

  R visitCastExpression(BPLCastExpression expr);

  R visitFunctionApplication(BPLFunctionApplication expr);

  R visitBoolLiteral(BPLBoolLiteral literal);

  R visitIntLiteral(BPLIntLiteral literal);

  R visitNullLiteral(BPLNullLiteral literal);

  R visitOldExpression(BPLOldExpression expr);
  
  /* R visitOldVariableExpression(BPLOldVariableExpression expr); */

  R visitQuantifierExpression(BPLQuantifierExpression expr);

  R visitLogicalNotExpression(BPLLogicalNotExpression expr);

  R visitUnaryMinusExpression(BPLUnaryMinusExpression expr);

  R visitVariableExpression(BPLVariableExpression expr);

  R visitTrigger(BPLTrigger trigger);

  R visitBuiltInType(BPLBuiltInType type);

  R visitTypeName(BPLTypeName type);

  R visitArrayType(BPLArrayType type);

  R visitParameterizedType(BPLParameterizedType type);
}
