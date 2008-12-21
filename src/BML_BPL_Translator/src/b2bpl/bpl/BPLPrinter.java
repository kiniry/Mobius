package b2bpl.bpl;

import java.io.PrintWriter;

import b2bpl.bpl.ast.BPLArrayExpression;
import b2bpl.bpl.ast.BPLArrayType;
import b2bpl.bpl.ast.BPLAssertCommand;
import b2bpl.bpl.ast.BPLAssignmentCommand;
import b2bpl.bpl.ast.BPLAssumeCommand;
import b2bpl.bpl.ast.BPLAxiom;
import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.bpl.ast.BPLBinaryArithmeticExpression;
import b2bpl.bpl.ast.BPLBinaryExpression;
import b2bpl.bpl.ast.BPLBinaryLogicalExpression;
import b2bpl.bpl.ast.BPLBoolLiteral;
import b2bpl.bpl.ast.BPLBuiltInType;
import b2bpl.bpl.ast.BPLCallCommand;
import b2bpl.bpl.ast.BPLCastExpression;
import b2bpl.bpl.ast.BPLCommand;
import b2bpl.bpl.ast.BPLCommentableNode;
import b2bpl.bpl.ast.BPLConstantDeclaration;
import b2bpl.bpl.ast.BPLDeclaration;
import b2bpl.bpl.ast.BPLEnsuresClause;
import b2bpl.bpl.ast.BPLEqualityExpression;
import b2bpl.bpl.ast.BPLExpression;
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
import b2bpl.bpl.ast.BPLNode;
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
import b2bpl.bpl.ast.BPLSpecificationClause;
import b2bpl.bpl.ast.BPLTrigger;
import b2bpl.bpl.ast.BPLTypeDeclaration;
import b2bpl.bpl.ast.BPLTypeName;
import b2bpl.bpl.ast.BPLUnaryExpression;
import b2bpl.bpl.ast.BPLUnaryMinusExpression;
import b2bpl.bpl.ast.BPLVariable;
import b2bpl.bpl.ast.BPLVariableDeclaration;
import b2bpl.bpl.ast.BPLVariableExpression;


public class BPLPrinter implements IBPLVisitor<Object> {

  protected final PrintWriter printer;

  protected final String eol = System.getProperty("line.separator");

  public BPLPrinter(PrintWriter printer) {
    this.printer = printer;
  }

  protected void print(String string) {
    printer.print(string);
  }

  protected void print(char character) {
    printer.print(character);
  }

  protected void print(int integer) {
    printer.print(integer);
  }

  protected void printNewLine() {
    printer.print(eol);
  }

  protected void printIndentation() {
    printer.print("  ");
  }

  protected void printList(BPLNode[] nodes) {
    if (nodes == null) return;
    for (int i = 0; i < nodes.length; i++) {
      if (i > 0) {
        print(", ");
      }
     
      nodes[i].accept(this);
    }
  }

  protected void printStringList(String[] strings) {
    if (strings == null) return;
    for (int i = 0; i < strings.length; i++) {
      if (i > 0) {
        print(", ");
      }
      print(strings[i]);
    }
  }

  protected void printOperandOf(BPLUnaryExpression expression) {
    BPLExpression operand = expression.getExpression();
    if (expression.getPrecedence().compare(operand.getPrecedence()) <= 0) {
      operand.accept(this);
    } else {
      print('(');
      operand.accept(this);
      print(')');
    }
  }

  protected void printLeftOperandOf(BPLBinaryExpression expression) {
    BPLExpression operand = expression.getLeft();
    if ((expression.getPrecedence().compare(operand.getPrecedence()) < 0)
        || expression.isLeftAssociativeTo(operand)) {
      operand.accept(this);
    } else {
      print('(');
      operand.accept(this);
      print(')');
    }
  }

  protected void printRightOperandOf(BPLBinaryExpression expression) {
    BPLExpression operand = expression.getRight();
    if ((expression.getPrecedence().compare(operand.getPrecedence()) < 0)
        || expression.isRightAssociativeTo(operand)) {
      operand.accept(this);
    } else {
      print('(');
      operand.accept(this);
      print(')');
    }
  }

  protected void printComments(BPLCommentableNode node, boolean indent) {
    for (String comment : node.getComments()) {
      if (indent) {
        printIndentation();
      }
      print("// ");
      print(comment);
      printNewLine();
    }
  }

  public Object visitProgram(BPLProgram program) {
    for (BPLDeclaration declaration : program.getDeclarations()) {
      printComments(declaration, false);
      declaration.accept(this);
      printNewLine();
      printNewLine();
    }
    return null;
  }

  public Object visitAxiom(BPLAxiom axiom) {
    print("axiom ");
    axiom.getExpression().accept(this);
    print(';');
    return null;
  }

  public Object visitConstantDeclaration(BPLConstantDeclaration declaration) {
    print("const unique ");
    printList(declaration.getConstants());
    print(';');
    return null;
  }

  public Object visitImplementation(BPLImplementation implementation) {
    print("implementation ");
    print(implementation.getProcedureName());

    print('(');
    printList(implementation.getInParameters());
    print(')');

    if (implementation.getOutParameters().length > 0) {
      print(" returns ");
      print('(');
      printList(implementation.getOutParameters());
      print(')');
    }

    printNewLine();
    implementation.getBody().accept(this);

    return null;
  }

  public Object visitProcedure(BPLProcedure procedure) {
    print("procedure ");
    print(procedure.getName());

    print('(');
    printList(procedure.getInParameters());
    print(')');

    if (procedure.getOutParameters().length > 0) {
      print(" returns ");
      print('(');
      printList(procedure.getOutParameters());
      print(')');
    }
   
    print(';');
    printNewLine();

    if (procedure.getSpecification() != null) {
      procedure.getSpecification().accept(this);
    }
    
    printNewLine();

    if (procedure.getImplementation() != null) {
      procedure.getImplementation().accept(this);
    }

    return null;
  }

  public Object visitTypeDeclaration(BPLTypeDeclaration declaration) {
    print("type ");
    printStringList(declaration.getTypeNames());
    print(';');
    return null;
  }

  public Object visitVariableDeclaration(BPLVariableDeclaration declaration) {
    print("var ");
    printList(declaration.getVariables());
    print(';');
    return null;
  }

  public Object visitVariable(BPLVariable variable) {
    print(variable.getName());
    print(": ");
    variable.getType().accept(this);
    if (variable.getWhereClause() != null) {
      print(" where ");
      variable.getWhereClause().accept(this);
    }
    return null;
  }

  public Object visitFunction(BPLFunction function) {
    print("function ");
    printStringList(function.getNames());

    print('(');
    printList(function.getInParameters());
    print(')');

    if (function.getOutParameter() != null) {
      print(" returns ");
      print('(');
      function.getOutParameter().accept(this);
      print(')');
    }
    print(';');

    return null;
  }

  public Object visitFunctionParameter(BPLFunctionParameter parameter) {
    if (parameter.getName() != null) {
      print(parameter.getName());
      print(": ");
    }
    parameter.getType().accept(this);
    return null;
  }

  public Object visitSpecification(BPLSpecification specification) {
    for (BPLSpecificationClause clause : specification.getClauses()) {
      printComments(clause, true);
      printIndentation();
      clause.accept(this);
      printNewLine();
    }
    return null;
  }

  public Object visitRequiresClause(BPLRequiresClause clause) {
    if (clause.isFree()) print("free ");
    print("requires ");
    clause.getExpression().accept(this);
    print(';');
    return null;
  }

  public Object visitModifiesClause(BPLModifiesClause clause) {
    print("modifies ");
    printList(clause.getVariables());
    print(';');
    return null;
  }

  public Object visitEnsuresClause(BPLEnsuresClause clause) {
    if (clause.isFree()) print("free ");
    print("ensures ");
    clause.getExpression().accept(this);
    print(';');
    return null;
  }

  public Object visitImplementationBody(BPLImplementationBody body) {
    print('{');

    if (body.getVariableDeclarations().length > 0) {
      printNewLine();
      for (BPLVariableDeclaration var : body.getVariableDeclarations()) {
        if (var.getVariables().length > 0) {
          printComments(var, true);
          printIndentation();
          var.accept(this);
          printNewLine();
        }
      }
    }

    for (BPLBasicBlock basicBlock : body.getBasicBlocks()) {
      printNewLine();
      printComments(basicBlock, true);
      basicBlock.accept(this);
    }

    print('}');

    return null;
  }

  public Object visitBasicBlock(BPLBasicBlock block) {
    print(block.getLabel());
    print(':');
    printNewLine();

    for (BPLCommand command : block.getCommands()) {
      printComments(command, true);
      printIndentation();
      command.accept(this);
      printNewLine();
    }

    printComments(block.getTransferCommand(), true);
    printIndentation();
    block.getTransferCommand().accept(this);
    printNewLine();

    return null;
  }

  public Object visitAssertCommand(BPLAssertCommand command) {
    print("assert ");
    if (command.getExpression() != null)
      command.getExpression().accept(this);
    else
      print("true");
    print(';');
    return null;
  }

  public Object visitAssumeCommand(BPLAssumeCommand command) {
    print("assume ");
    if (command.getExpression() != null)
      command.getExpression().accept(this);
    else
      print("true");
    print(';');
    return null;
  }

  public Object visitAssignmentCommand(BPLAssignmentCommand command) {
    command.getLeft().accept(this);
    print(" := ");
    command.getRight().accept(this);
    print(';');
    return null;
  }

  public Object visitCallCommand(BPLCallCommand command) {
    print("call ");

    if (command.getResultVariables().length > 0) {
      printList(command.getResultVariables());
      print(" := ");
    }

    print(command.getProcedureName());
    print('(');
    printList(command.getArguments());
    print(')');
    print(';');

    return null;
  }

  public Object visitHavocCommand(BPLHavocCommand command) {
    print("havoc ");
    printList(command.getVariables());
    print(';');
    return null;
  }

  public Object visitGotoCommand(BPLGotoCommand command) {
    print("goto ");
    printStringList(command.getTargetLabels());
    print(';');
    return null;
  }

  public Object visitReturnCommand(BPLReturnCommand command) {
    print("return;");
    return null;
  }

  public Object visitArrayExpression(BPLArrayExpression expr) {
    expr.getPrefix().accept(this);
    print('[');
    printList(expr.getAccessors());
    print(']');
    return null;
  }

  public Object visitBinaryArithmeticExpression(
      BPLBinaryArithmeticExpression expr) {
    printLeftOperandOf(expr);
    switch (expr.getOperator()) {
      case PLUS:
        print(" + ");
        break;
      case MINUS:
        print(" - ");
        break;
      case TIMES:
        print(" * ");
        break;
      case DIVIDE:
        print(" / ");
        break;
      case REMAINDER:
      default:
        print(" % ");
        break;
    }
    printRightOperandOf(expr);

    return null;
  }

  public Object visitBinaryLogicalExpression(BPLBinaryLogicalExpression expr) {
    printLeftOperandOf(expr);
    switch (expr.getOperator()) {
      case AND:
        print(" && ");
        break;
      case OR:
        print(" || ");
        break;
      case IMPLIES:
        print(" ==> ");
        break;
      case EQUIVALENCE:
      default:
        print(" <==> ");
        break;
    }
    printRightOperandOf(expr);

    return null;
  }

  public Object visitEqualityExpression(BPLEqualityExpression expr) {
    printLeftOperandOf(expr);
    switch (expr.getOperator()) {
      case EQUALS:
        print(" == ");
        break;
      case NOT_EQUALS:
      default:
        print(" != ");
        break;
    }
    printRightOperandOf(expr);

    return null;
  }

  public Object visitPartialOrderExpression(BPLPartialOrderExpression expr) {
    printLeftOperandOf(expr);
    print(" <: ");
    printRightOperandOf(expr);
    return null;
  }

  public Object visitRelationalExpression(BPLRelationalExpression expr) {
    printLeftOperandOf(expr);
    switch (expr.getOperator()) {
      case LESS:
        print(" < ");
        break;
      case GREATER:
        print(" > ");
        break;
      case LESS_EQUAL:
        print(" <= ");
        break;
      case GREATER_EQUAL:
      default:
        print(" >= ");
        break;
    }
    printRightOperandOf(expr);

    return null;
  }

  public Object visitCastExpression(BPLCastExpression expr) {
    print("cast");
    print('(');
    expr.getExpression().accept(this);
    print(", ");
    expr.getTargetType().accept(this);
    print(')');
    return null;
  }

  public Object visitFunctionApplication(BPLFunctionApplication expr) {
    print(expr.getFunctionName());
    print('(');
    printList(expr.getArguments());
    print(')');
    return null;
  }

  public Object visitBoolLiteral(BPLBoolLiteral literal) {
    print(literal.getValue() ? "true" : "false");
    return null;
  }

  public Object visitIntLiteral(BPLIntLiteral literal) {
    print(literal.getValue());
    return null;
  }

  public Object visitNullLiteral(BPLNullLiteral literal) {
    print("null");
    return null;
  }

  public Object visitOldExpression(BPLOldExpression expr) {
    print("old");
    print('(');
    expr.getExpression().accept(this);
    print(')');
    return null;
  }

  public Object visitQuantifierExpression(BPLQuantifierExpression expr) {
    print('(');
    switch (expr.getOperator()) {
      case FORALL:
        print("forall");
        break;
      case EXISTS:
      default:
        print("exists");
        break;
    }
    print(' ');
    printList(expr.getVariables());
    print(" :: ");
    for (BPLTrigger trigger : expr.getTriggers()) {
      if (trigger != null) {
        trigger.accept(this);
        print(' ');
      }
    }
    expr.getExpression().accept(this);
    print(')');

    return null;
  }

  public Object visitLogicalNotExpression(BPLLogicalNotExpression expr) {
    print('!');
    printOperandOf(expr);
    return null;
  }

  public Object visitUnaryMinusExpression(BPLUnaryMinusExpression expr) {
    print('-');
    printOperandOf(expr);
    return null;
  }

  public Object visitVariableExpression(BPLVariableExpression expr) {
    print(expr.getIdentifier());
    return null;
  }
  
  /*
  public Object visitOldVariableExpression(BPLOldVariableExpression expr) {
    print("\\old(");
    print(expr.getIdentifier());
    print(")");
    return null;
  }
  */

  public Object visitTrigger(BPLTrigger trigger) {
    print("{ ");
    printList(trigger.getExpressions());
    print(" }");  
    return null;
  }

  public Object visitBuiltInType(BPLBuiltInType type) {
    print(type.getName());
    return null;
  }

  public Object visitTypeName(BPLTypeName type) {
    print(type.getName());
    return null;
  }

  public Object visitArrayType(BPLArrayType type) {
    print('[');
    printList(type.getIndexTypes());
    print(']');
    type.getElementType().accept(this);
    return null;
  }

  public Object visitParameterizedType(BPLParameterizedType type) {
    print('<');
    type.getParameterType().accept(this);
    print('>');
    type.getType().accept(this);
    return null;
  }
}
