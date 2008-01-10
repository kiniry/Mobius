/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.rules;

import jml2bml.bmllib.BmlLibUtils;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.engine.Symbols;
import jml2bml.engine.UniqueIndexGenerator;
import jml2bml.engine.Utils;
import jml2bml.engine.Variable;
import jml2bml.exceptions.NotTranslatedException;

import org.apache.bcel.classfile.JavaClass;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import annot.bcclass.BCClass;
import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.ArrayAccess;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.ConditionalExpression;
import annot.bcexpression.FieldAccess;
import annot.bcexpression.NULL;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.THIS;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.formula.Predicate2Ar;
import annot.bcexpression.formula.QuantifiedFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.io.ReadAttributeException;

import com.sun.source.tree.ArrayAccessTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberSelectTree;
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
  private final Context context;

  private boolean isOld = true;

  public ExpressionRule(final Context context) {
    this.context = context;
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
    final String name = node.getName().toString();
    final BCClass clazz = context.get(BCClass.class);
    System.out.println(name);
    if ("this".equals(name)) {
      return new THIS(isOld, clazz);
    }
    final Variable variable = p.get(name);
    if (variable == null) {
      return null;
      //throw new RuntimeException("Invalid variable " + name);
    }
    if (variable.isBoundVariable()) {
      return variable.getVariable();
    }
    if (variable.isLocalVariable()) {
      return variable.getVariable();
    }
    if (variable.isField()) {
      //field access is handled in a different way:
      //(cannot be taken from the symbol table, we have to know, 
      //whether it's old or not
      return BytecodeUtil.createFieldRef(isOld, name, clazz);
    }
    return null;
  };

  /**
   * This method handles the Literal node.
   * @param node - node to handle
   * @param p - symbol table at this point
   *
   * @return parsed Literal. Currently only int,
   * boolean and null-literals are parsed
   */
  @Override
  public BCExpression visitLiteral(final LiteralTree node, final Symbols p) {
    final Kind kind = node.getKind();
    if (kind == Kind.INT_LITERAL) {
      return new NumberLiteral(((Integer) node.getValue()).intValue());
    }
    if (kind == Kind.BOOLEAN_LITERAL) {
      return new Predicate0Ar(((Boolean) node.getValue()).booleanValue());
    }
    if (kind == Kind.NULL_LITERAL) {
      return new NULL();
    }
    throw new NotTranslatedException("Not implemented literal: " + node);
  };

  /**
   * Handling conditional expressions ( cond ? trueExpr : falseExpr ).
   * @param node - node to parse
   * @param p - symbol table at current point
   * @return parsed expression
   */
  @Override
  public BCExpression visitConditionalExpression(
                                                 final ConditionalExpressionTree node,
                                                 final Symbols p) {
    final BCExpression condition = scan(node.getCondition(), p);
    final BCExpression trueExpr = scan(node.getTrueExpression(), p);
    final BCExpression falseExpr = scan(node.getFalseExpression(), p);
    return new ConditionalExpression(condition, trueExpr, falseExpr);

  }

  @Override
  public BCExpression visitParenthesized(final ParenthesizedTree node,
                                         final Symbols p) {
    return scan(node.getExpression(), p);
  }

  /**
   * Handling quantified expressions.
   * @param node - node to parse
   *= @param p - sybmol table at this point
   * (it will be extended here, by addind bounded variables)
   * @return parsed expression
   */
  @Override
  public BCExpression visitJmlQuantifiedExpr(final JmlQuantifiedExpr node,
                                             final Symbols p) {
    final int quantifierType = Utils.mapJCOperatorToBmlLib(node.op);
    final QuantifiedFormula formula = new QuantifiedFormula(quantifierType);
    final JavaBasicType type = (JavaBasicType) scan(node.localtype, p);
    final Symbols symbols = new Symbols(p);
    for (Name name : node.names) {
      final BoundVar var = new BoundVar(type, UniqueIndexGenerator.getNext(),
                                        formula, name.toString());
      formula.addVariable(var);
      symbols.put(name.toString(), new Variable(var, node));
    }
    final BCExpression predicate = scan(node.predicate, symbols);
    formula.setFormula(predicate);
    return formula;
  }

  /*FIXME: (kjk) Is this method needed (we have visitBinary,
   *maybe that one should be moved to this one??
   *[JF] yes, this is needed. I think there are cases,
   *where visitJmlBinary is invoked and visitBinary - not
   */
  @Override
  public BCExpression visitJmlBinary(final JmlBinary node, final Symbols p) {
    final BCExpression lhs = scan(node.getLeftOperand(), p);
    final BCExpression rhs = scan(node.getRightOperand(), p);
    final int operator = Utils.mapJCOperatorToBmlLib(node.op);
    return new ArithmeticExpression(operator, lhs, rhs);
  }

  @Override
  public BCExpression visitPrimitiveType(final PrimitiveTypeTree node,
                                         final Symbols p) {
    try {
      return JavaType.getJavaBasicType(Utils.mapJCTypeKindToBmlLib(node
          .getPrimitiveTypeKind()));
    } catch (ReadAttributeException e) {
      throw new RuntimeException(e);
    }

  }

  @Override
  public BCExpression visitMemberSelect(final MemberSelectTree node,
                                        final Symbols p) {
    final BCExpression expr = scan(node.getExpression(), p);
    
    return new FieldAccess(Code.FIELD_ACCESS, expr, expr);
    //FIXME!!!
  }

  /**
   * Handling array access a[k].
   * @param node - node to translate
   * @param p - symbol table
   * @return parsed node
   */
  @Override
  public BCExpression visitArrayAccess(final ArrayAccessTree node,
                                       final Symbols p) {
    return new ArrayAccess(scan(node.getExpression(), p), scan(node.getIndex(),
                                                               p));
  }
}
