/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-08 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bmllib;

import javax.lang.model.type.TypeKind;

import jml2bml.engine.Symbols;
import jml2bml.exceptions.NotTranslatedException;
import jml2bml.rules.RulesFactory;

import org.jmlspecs.openjml.JmlToken;

import annot.bcclass.BCClass;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldRef;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.io.Code;

import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 * @author Jedrek (fulara@mimuw.edu.pl)
 *
 */
final public class BmlLibUtils {
  /**
   * Hidden constructor (util class).
   */
  private BmlLibUtils() {
  }

  /**
   * Returns true iff the given operator is a 2 argument predicate.
   * @param operator - checked operator
   * @return if the operator is a 2-arg predicate
   */
  public static boolean isBinaryOperatorPredicate2Ar(final int operator) {
    switch (operator) {
    case Code.GRT:
    case Code.GRTEQ:
    case Code.LESS:
    case Code.LESSEQ:
    case Code.EQ:
    case Code.NOTEQ:
    case Code.AND:
    case Code.OR:
    case Code.IMPLIES:
      return true;
    default:
      return false;
    }
  }

  /**
   * Translates a binary operator from the OpenJml Constant to BmlLib constant.
   * @param kind - OpenJML constant
   * @return - BmlLib constant
   */
  public static int translateBinaryOperator(final Kind kind) {
    //TODO: check if all translated ok
    if (kind == Kind.AND)
      return Code.AND;
    if (kind == Kind.DIVIDE)
      return Code.DIV;
    if (kind == Kind.EQUAL_TO)
      return Code.EQ;
    if (kind == Kind.GREATER_THAN)
      return Code.GRT;
    if (kind == Kind.GREATER_THAN_EQUAL)
      return Code.GRTEQ;
    if (kind == Kind.LEFT_SHIFT)
      return Code.SHL;
    if (kind == Kind.LESS_THAN)
      return Code.LESS;
    if (kind == Kind.LESS_THAN_EQUAL)
      return Code.LESSEQ;
    if (kind == Kind.MINUS)
      return Code.MINUS;
    if (kind == Kind.MULTIPLY)
      return Code.MULT;
    if (kind == Kind.NOT_EQUAL_TO)
      return Code.NOTEQ;
    if (kind == Kind.OR)
      return Code.OR;
    if (kind == Kind.PLUS)
      return Code.PLUS;
    if (kind == Kind.REMAINDER)
      return Code.REM;
    if (kind == Kind.RIGHT_SHIFT)
      return Code.SHR;
    if (kind == Kind.CONDITIONAL_AND)
      return Code.AND;
    if (kind == Kind.CONDITIONAL_OR)
      return Code.OR;

    //    if (kind == Kind.UNSIGNED_RIGHT_SHIFT) return
    //    if (kind == Kind.XOR) return 
    throw new RuntimeException("Not implemented binary operator: " + kind);
  }

  public static int mapJCTagToBmlLib(int tag) {
    if (tag == JCTree.AND) {
      return Code.AND;
    }
    if (tag == JCTree.OR) {
      return Code.OR;
    }
    //FIXME
    return -3;
  }

  public static String mapJCTypeKindToBmlLib(TypeKind primitiveTypeKind) {
    if (TypeKind.BOOLEAN.compareTo(primitiveTypeKind) == 0) {
      return "boolean";
    }
    if (TypeKind.INT.compareTo(primitiveTypeKind) == 0) {
      return "int";
    }
    //FIXME
    return null;
  }

  public static int mapJCOperatorToBmlLib(JmlToken token) {
    if (JmlToken.BSFORALL.equals(token))
      return Code.FORALL_WITH_NAME;
    if (JmlToken.BSEXISTS.equals(token))
      return Code.EXISTS_WITH_NAME;
    if (JmlToken.IMPLIES.equals(token))
      return Code.IMPLIES;
    //FIXME
    return 0;
  }

  public static FieldRef createFieldRef(boolean isOld, int index,
                                        Symbols symbols) {
    BCClass clazz = symbols.findClass();
    return new FieldRef(isOld, clazz.getCp(), index);
  }

  public static AbstractFormula getFormula(JCExpression expression,
                                           Symbols symb, Context context) {
    if (expression == null)
      return null;
    final BCExpression bcExpr = expression.accept(RulesFactory
        .getExpressionRule(context), symb);
    if (bcExpr.getType1() != JavaBasicType.JavaBool)
      throw new NotTranslatedException("assert expression must be boolean");
    return (AbstractFormula) bcExpr;
  }
}
