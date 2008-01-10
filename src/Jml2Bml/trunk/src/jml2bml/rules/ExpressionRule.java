/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import jml2bml.bmllib.BmlLibUtils;
import jml2bml.engine.Symbols;
import jml2bml.engine.UniqueIndexGenerator;
import jml2bml.engine.Utils;
import jml2bml.engine.Variable;
import jml2bml.exceptions.NotTranslatedException;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.ArrayAccess;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.ConditionalExpression;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.formula.Predicate2Ar;
import annot.bcexpression.formula.QuantifiedFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.ReadAttributeException;

import com.sun.source.tree.ArrayAccessTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.ParenthesizedTree;
import com.sun.source.tree.PrimitiveTypeTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;

/**
 * Rule for translating JML expressions.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @author kjk    (kjk@mimuw.edu.pl)
 *
 */
public class ExpressionRule extends TranslationRule<BCExpression, Symbols> {

  public ExpressionRule(final Context context) {
  }

  // ------- visitor methods
  // TODO probably more nodes should be visited here
  @Override
  public BCExpression visitBinary(BinaryTree node, Symbols p) {
    BCExpression lhs = scan(node.getLeftOperand(), p);
    BCExpression rhs = scan(node.getRightOperand(), p);
    int operator = BmlLibUtils.translateBinaryOperator(node.getKind());
    //TODO: (kjk) This should be done better!!
    if (BmlLibUtils.isBinaryOperatorPredicate2Ar(operator))
      return new Predicate2Ar(operator, lhs, rhs);
    else
      return new ArithmeticExpression(operator, lhs, rhs);
  }

  @Override
  public BCExpression visitIdentifier(IdentifierTree node, Symbols p) {
    // FIXME translate identifier properly!
    String name = node.getName().toString();
    Variable variable = p.get(name);
    System.out.println(name);
    if (variable == null) {
      return null;
      //throw new RuntimeException("Invalid variable " + name);
    }
    if (variable.isBoundVariable()) {
      return variable.getVariable();
    }
    //TODO handle other cases;
    return null;
  };

  @Override
  public BCExpression visitLiteral(LiteralTree node, Symbols p) {
    System.out.println(node);
    Kind kind = node.getKind();
    if (kind == Kind.INT_LITERAL)
      return new NumberLiteral(((Integer) node.getValue()).intValue());
    if (kind == Kind.BOOLEAN_LITERAL)
      return new Predicate0Ar(((Boolean)node.getValue()).booleanValue());
    throw new NotTranslatedException("Not implemented literal: " + node);
  };

  @Override
  public BCExpression visitConditionalExpression(ConditionalExpressionTree node,
                                           Symbols p) {
    BCExpression condition = scan(node.getCondition(), p);
    BCExpression trueExpr = scan(node.getTrueExpression(), p);
    BCExpression falseExpr = scan(node.getFalseExpression(), p);
    return new ConditionalExpression(condition, trueExpr, falseExpr);

  }

  @Override
  public BCExpression visitParenthesized(ParenthesizedTree node, Symbols p) {
    return scan(node.getExpression(), p);
  }

  @Override
  public BCExpression visitJmlQuantifiedExpr(JmlQuantifiedExpr node, Symbols p) {
    int quantifierType = Utils.mapJCOperatorToBmlLib(node.op);
    QuantifiedFormula formula = new QuantifiedFormula(quantifierType);
    JavaBasicType type = (JavaBasicType)scan(node.localtype, p);
    Symbols symbols = new Symbols(p);
    for (Name name : node.names) {
      BoundVar var = new BoundVar(type, UniqueIndexGenerator.getNext(), formula, name.toString());
      formula.addVariable(var);
      symbols.put(name.toString(), new Variable(var, node));
    }
    final BCExpression predicate = scan(node.predicate, symbols);
    formula.setFormula(predicate);
    return formula;
  }

  //FIXME: (kjk) Is this method needed (we have visitBinary, maybe that one should be moved to this one??
  //[JF] yes, this is needed. I think there are cases, where visitJmlBinary is invoked and visitBinary - not
  @Override
  public BCExpression visitJmlBinary(JmlBinary node, Symbols p) {
    BCExpression lhs = scan(node.getLeftOperand(), p);
    BCExpression rhs = scan(node.getRightOperand(), p);
    int operator = Utils.mapJCOperatorToBmlLib(node.op);
    return new ArithmeticExpression(operator, lhs, rhs);
  }
  
  @Override
  public BCExpression visitPrimitiveType(PrimitiveTypeTree node, Symbols p) {
    try {
      return JavaType.getJavaBasicType(Utils.mapJCTypeKindToBmlLib(node.getPrimitiveTypeKind()));
    } catch (ReadAttributeException e) {
      throw new RuntimeException(e);
    }
    
  }
  
  @Override
  public BCExpression visitArrayAccess(ArrayAccessTree node, Symbols p) {
    return new ArrayAccess(scan(node.getExpression(), p), scan(node.getIndex(), p));
  }
}
