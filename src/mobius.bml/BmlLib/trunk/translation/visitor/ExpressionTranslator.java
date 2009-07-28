package visitor;

import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldAccess;
import annot.bcexpression.FieldRef;
import annot.bcexpression.LocalVariable;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.RESULT;
import annot.bcexpression.SingleOccurence;
import annot.bcexpression.THIS;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.formula.Predicate2Ar;
import annot.bcexpression.javatype.JavaArrayType;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import b2bpl.bytecode.JBaseType;
import b2bpl.bytecode.JReferenceType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.ast.BMLExpression;

public class ExpressionTranslator  {
  public ExpressionTranslator() {

  }

  public b2bpl.bytecode.bml.ast.BMLExpression visitPredicate0Ar(
                                                                Predicate0Ar constant) {
    if (constant.getValue())
      return b2bpl.bytecode.bml.ast.BMLBooleanLiteral.TRUE;
    return b2bpl.bytecode.bml.ast.BMLBooleanLiteral.FALSE;
  }

  public b2bpl.bytecode.bml.ast.BMLExpression visitResult(RESULT result) {
    return b2bpl.bytecode.bml.ast.BMLResultExpression.RESULT;
  }

  public b2bpl.bytecode.bml.ast.BMLExpression visitSingleOccurence(
                                                                   SingleOccurence expr) {
    return visit(expr.getSharedExpr());
  }

  public b2bpl.bytecode.bml.ast.BMLExpression visitLocalVariable(
                                                                 LocalVariable var) {
    return new b2bpl.bytecode.bml.ast.BMLLocalVariableExpression(var.getIndex());
  }

  public b2bpl.bytecode.bml.ast.BMLExpression visitNumberLiteral(
                                                                 NumberLiteral number) {
    return new b2bpl.bytecode.bml.ast.BMLIntLiteral(number.getValue());
  }

  public b2bpl.bytecode.bml.ast.BMLExpression visitPredicate2Ar(
                                                                Predicate2Ar predicate) {
    int connector = predicate.getConnector();
    BCExpression[] exprs = predicate.getAllSubExpr();
    b2bpl.bytecode.bml.ast.BMLExpression left = visit(exprs[0]);
    System.out.println("To jest lewy " + left);
    b2bpl.bytecode.bml.ast.BMLExpression right = visit(exprs[1]);
    System.out.println("To jest prawy " + right);
    switch (connector) {
    case Code.GRT:
      return new b2bpl.bytecode.bml.ast.BMLRelationalExpression(
                                                                b2bpl.bytecode.bml.ast.BMLRelationalExpression.Operator.GREATER,
                                                                left, right);
    case Code.LESS:
      return new b2bpl.bytecode.bml.ast.BMLRelationalExpression(
                                                                b2bpl.bytecode.bml.ast.BMLRelationalExpression.Operator.LESS,
                                                                left, right);
    case Code.LESSEQ:
      return new b2bpl.bytecode.bml.ast.BMLRelationalExpression(
                                                                b2bpl.bytecode.bml.ast.BMLRelationalExpression.Operator.LESS_EQUAL,
                                                                left, right);
    case Code.GRTEQ:
      return new b2bpl.bytecode.bml.ast.BMLRelationalExpression(
                                                                b2bpl.bytecode.bml.ast.BMLRelationalExpression.Operator.GREATER_EQUAL,
                                                                left, right);
    case Code.EQ:
      return new b2bpl.bytecode.bml.ast.BMLEqualityExpression(
                                                              b2bpl.bytecode.bml.ast.BMLEqualityExpression.Operator.EQUALS,
                                                              left, right);
    case Code.NOTEQ:
      return new b2bpl.bytecode.bml.ast.BMLEqualityExpression(
                                                              b2bpl.bytecode.bml.ast.BMLEqualityExpression.Operator.NOT_EQUALS,
                                                              left, right);

    }
    return doVisitArithmeticExpression(connector, left, right);
  }
  private b2bpl.bytecode.bml.ast.BMLExpression  doVisitArithmeticExpression(int connector, b2bpl.bytecode.bml.ast.BMLExpression left, b2bpl.bytecode.bml.ast.BMLExpression right){
    switch (connector){
    case Code.MULT:
      return new b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression(b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression.Operator.TIMES,
                                                                      left, right);
    case Code.DIV :
      return new b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression(b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression.Operator.DIVIDE,
                                                                      left, right);
    case Code.PLUS :
      return new b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression(b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression.Operator.PLUS,
                                                                      left, right);
    case Code.MINUS :
      return new b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression(b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression.Operator.MINUS,
                                                                      left, right);
    case Code.REM :
      return new b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression(b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression.Operator.REMAINDER,
                                                                      left, right);
    }
    return null;
  }
  public b2bpl.bytecode.bml.ast.BMLExpression visitArithmeticExpression(ArithmeticExpression expr){
    int connector = expr.getConnector();
    BCExpression[] exprs = expr.getAllSubExpr();
    b2bpl.bytecode.bml.ast.BMLExpression left = visit(exprs[0]);
    System.out.println("To jest lewy " + left);
    b2bpl.bytecode.bml.ast.BMLExpression right = visit(exprs[1]);
    System.out.println("To jest prawy " + right);
    return doVisitArithmeticExpression(connector, left, right);
  }
  public b2bpl.bytecode.bml.ast.BMLExpression visitThis(THIS expr) {
    return b2bpl.bytecode.bml.ast.BMLThisExpression.THIS;
  }

  public b2bpl.bytecode.bml.ast.BMLFieldExpression visitFieldRef(
                                                                 FieldRef ref,
                                                                 JReferenceType owner) {
    JavaType type = ref.getType1();
    JType rtype = null;
    if (type instanceof JavaReferenceType) {
      rtype = JType.fromDescriptor(((JavaReferenceType) type).getSignature());
    }
    if (type instanceof JavaArrayType) {
      rtype = JType.fromDescriptor(((JavaArrayType) type).getSignature());
    }
    if (type instanceof JavaBasicType) {
      JavaBasicType bt = (JavaBasicType) type;
      if (bt.compareTypes(JavaBasicType.JAVA_BOOLEAN_TYPE) == JavaBasicType.TYPES_EQUAL)
        rtype = JBaseType.BOOLEAN;
      else
        rtype = JBaseType.INT;
    }
    String name = ref.getName();
    return new b2bpl.bytecode.bml.ast.BMLFieldExpression(owner, name, rtype);
  }

  public b2bpl.bytecode.bml.ast.BMLExpression visitFieldAccess(FieldAccess expr) {
    BCExpression[] e = expr.getAllSubExpr();
    System.out.println(e[1].getClass().getName());
    BMLExpression owner = visit(e[0]);

    BMLExpression res = new b2bpl.bytecode.bml.ast.BMLFieldAccessExpression(
                                                                            owner,
                                                                            visitFieldRef(
                                                                                          (FieldRef) e[1],
                                                                                          (JReferenceType) owner
                                                                                              .getType()));
    return res;
  }

  public b2bpl.bytecode.bml.ast.BMLExpression visit(BCExpression expr) {
    if (expr instanceof Predicate0Ar)
      return visitPredicate0Ar((Predicate0Ar) expr);
    if (expr instanceof Predicate2Ar)
      return visitPredicate2Ar((Predicate2Ar) expr);
    if (expr instanceof RESULT)
      return visitResult((RESULT) expr);
    if (expr instanceof SingleOccurence)
      return visitSingleOccurence((SingleOccurence) expr);
    if (expr instanceof LocalVariable)
      return visitLocalVariable((LocalVariable) expr);
    if (expr instanceof NumberLiteral)
      return visitNumberLiteral((NumberLiteral) expr);
    if (expr instanceof FieldAccess)
      return visitFieldAccess((FieldAccess) expr);
    if (expr instanceof THIS)
      return visitThis((THIS) expr);
    if (expr instanceof ArithmeticExpression)
      return visitArithmeticExpression((ArithmeticExpression)expr);
    if (expr instanceof FieldRef)
      //FIXME null?
      return visitFieldRef((FieldRef) expr, null);
    return null;
  }

}
