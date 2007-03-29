package b2bpl.bytecode.bml;

import b2bpl.bytecode.bml.ast.BMLArrayAccessExpression;
import b2bpl.bytecode.bml.ast.BMLArrayLengthExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryBitwiseExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryLogicalExpression;
import b2bpl.bytecode.bml.ast.BMLBooleanLiteral;
import b2bpl.bytecode.bml.ast.BMLBoundVariableExpression;
import b2bpl.bytecode.bml.ast.BMLCastExpression;
import b2bpl.bytecode.bml.ast.BMLElemTypeExpression;
import b2bpl.bytecode.bml.ast.BMLEqualityExpression;
import b2bpl.bytecode.bml.ast.BMLFieldAccessExpression;
import b2bpl.bytecode.bml.ast.BMLFieldExpression;
import b2bpl.bytecode.bml.ast.BMLFreshExpression;
import b2bpl.bytecode.bml.ast.BMLInstanceOfExpression;
import b2bpl.bytecode.bml.ast.BMLIntLiteral;
import b2bpl.bytecode.bml.ast.BMLLocalVariableExpression;
import b2bpl.bytecode.bml.ast.BMLLogicalNotExpression;
import b2bpl.bytecode.bml.ast.BMLNullLiteral;
import b2bpl.bytecode.bml.ast.BMLOldExpression;
import b2bpl.bytecode.bml.ast.BMLPredicate;
import b2bpl.bytecode.bml.ast.BMLQuantifierExpression;
import b2bpl.bytecode.bml.ast.BMLRelationalExpression;
import b2bpl.bytecode.bml.ast.BMLResultExpression;
import b2bpl.bytecode.bml.ast.BMLStackCounterExpression;
import b2bpl.bytecode.bml.ast.BMLStackElementExpression;
import b2bpl.bytecode.bml.ast.BMLThisExpression;
import b2bpl.bytecode.bml.ast.BMLTypeOfExpression;
import b2bpl.bytecode.bml.ast.BMLUnaryMinusExpression;


/**
 * Visitor for BML specification expressions.
 *
 * @param <R>  Type parameter specifying the return type declared on all the
 *             methods of the visitor.
 *
 * @author Ovidio Mallo
 */
public interface BMLExpressionVisitor<R> {

  R visitQuantifierExpression(BMLQuantifierExpression expr);

  R visitBinaryArithmeticExpression(BMLBinaryArithmeticExpression expr);

  R visitBinaryLogicalExpression(BMLBinaryLogicalExpression expr);

  R visitEqualityExpression(BMLEqualityExpression expr);

  R visitRelationalExpression(BMLRelationalExpression expr);

  R visitBinaryBitwiseExpression(BMLBinaryBitwiseExpression expr);

  R visitUnaryMinusExpression(BMLUnaryMinusExpression expr);

  R visitLogicalNotExpression(BMLLogicalNotExpression expr);

  R visitInstanceOfExpression(BMLInstanceOfExpression expr);

  R visitCastExpression(BMLCastExpression expr);

  R visitBooleanLiteral(BMLBooleanLiteral literal);

  R visitIntLiteral(BMLIntLiteral literal);

  R visitNullLiteral(BMLNullLiteral literal);

  R visitLocalVariableExpression(BMLLocalVariableExpression expr);

  R visitBoundVariableExpression(BMLBoundVariableExpression expr);

  R visitStackElementExpression(BMLStackElementExpression expr);

  R visitStackCounterExpression(BMLStackCounterExpression expr);

  R visitOldExpression(BMLOldExpression expr);

  R visitPredicate(BMLPredicate predicate);

  R visitFieldExpression(BMLFieldExpression expr);

  R visitFieldAccessExpression(BMLFieldAccessExpression expr);

  R visitArrayAccessExpression(BMLArrayAccessExpression expr);

  R visitArrayLengthExpression(BMLArrayLengthExpression expr);

  R visitTypeOfExpression(BMLTypeOfExpression expr);

  R visitElemTypeExpression(BMLElemTypeExpression expr);

  R visitResultExpression(BMLResultExpression expr);

  R visitThisExpression(BMLThisExpression expr);

  R visitFreshExpression(BMLFreshExpression expr);
}
