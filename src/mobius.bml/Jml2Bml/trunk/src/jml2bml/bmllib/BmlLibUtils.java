/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-08 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bmllib;

import javax.lang.model.type.TypeKind;

import jml2bml.exceptions.Jml2BmlException;

import org.jmlspecs.openjml.JmlToken;

import annot.bcclass.BCClass;
import annot.bcexpression.FieldRef;
import annot.io.Code;

import com.sun.source.tree.Tree.Kind;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0-0.1
 */
public final class BmlLibUtils {
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
      case Code.EQUIV:
        return true;
      default:
        return false;
    }
  }
  
  public static int translateUnaryOperator(final Kind kind) {
    if (kind == Kind.LOGICAL_COMPLEMENT)
      return Code.NEG;
    throw new Jml2BmlException("Not implemented unary operator: " + kind);    
  }

  /**
   * Translates a binary operator from the OpenJml Constant to BmlLib constant.
   * @param kind - OpenJML constant
   * @return - BmlLib constant
   */
  public static int translateBinaryOperator(final Kind kind) {
    //TODO: check if all translated ok
    int ret = booleanOperator(kind);
    if (ret == -1) {
      ret = arithmeticOperator(kind);
    }
    if (ret == -1) {
      ret = bitOperator(kind);
    }
    if (ret != -1) {
      return ret;
    }

    throw new Jml2BmlException("Not implemented binary operator: " + kind);

  }

  /**
   * Tries to recognize and translate arithmetic operator.
   * @param kind operator to translate
   * @return translated operator
   */
  private static int arithmeticOperator(final Kind kind) {
    int ret = -1;
    if (kind == Kind.DIVIDE) {
      ret = Code.DIV;
    }
    if (kind == Kind.MINUS) {
      ret = Code.MINUS;
    }
    if (kind == Kind.MULTIPLY) {
      ret = Code.MULT;
    }
    if (kind == Kind.PLUS) {
      ret = Code.PLUS;
    }
    if (kind == Kind.REMAINDER) {
      ret = Code.REM;
    }
    return ret;
  }

  /**
   * Tries to recognize and translate bit operator.
   * @param kind operator to translate
   * @return translated operator
   */
  private static int bitOperator(final Kind kind) {
    int ret = -1;
    if (kind == Kind.LEFT_SHIFT) {
      ret = Code.SHL;
    }
    if (kind == Kind.RIGHT_SHIFT) {
      ret = Code.SHR;
    }
    return ret;
  }

  /**
   * Tries to translate boolean operator.
   * @param kind operator to translate
   * @return translated operator
   */
  private static int booleanOperator(final Kind kind) {
    int ret = relationalOperator(kind);
    if (kind == Kind.AND) {
      ret = Code.AND;
    }
    if (kind == Kind.OR || kind == Kind.CONDITIONAL_OR) {
      ret = Code.OR;
    }
    if (kind == Kind.CONDITIONAL_AND) {
      ret = Code.AND;
    }
    return ret;
  }

  /**
   * Tries to recognize and translate relational operator.
   * @param kind operator to translate
   * @return translated operator
   */
  private static int relationalOperator(final Kind kind) {
    int ret = -1;
    if (kind == Kind.EQUAL_TO) {
      ret = Code.EQ;
    }
    if (kind == Kind.GREATER_THAN) {
      ret = Code.GRT;
    }
    if (kind == Kind.GREATER_THAN_EQUAL) {
      ret = Code.GRTEQ;
    }
    if (kind == Kind.LESS_THAN) {
      ret = Code.LESS;
    }
    if (kind == Kind.LESS_THAN_EQUAL) {
      ret = Code.LESSEQ;
    }
    if (kind == Kind.NOT_EQUAL_TO) {
      ret = Code.NOTEQ;
    }
    return ret;
  }

  /**
   * Translates JC primitive type to BmlLib primitive type.
   * If the type is not recognized, throws an exception
   * @param primitiveTypeKind type to translate
   * @return translated type name
   */
  public static String mapJCTypeKindToBmlLib(final TypeKind primitiveTypeKind) {
    if (TypeKind.BOOLEAN.compareTo(primitiveTypeKind) == 0) {
      return "boolean";
    }
    if (TypeKind.INT.compareTo(primitiveTypeKind) == 0) {
      return "int";
    }
    throw new Jml2BmlException("Unrecognized type " + primitiveTypeKind);
  }

  /**
   * Translates JC operator to BmlLib operator.
   * @param token operator to translate
   * @return translated operator
   */
  public static int mapJCOperatorToBmlLib(final JmlToken token) {
    int res = -1;
    if (JmlToken.BSFORALL.equals(token))
      res = Code.FORALL_WITH_NAME;
    if (JmlToken.BSEXISTS.equals(token))
      res = Code.EXISTS_WITH_NAME;
    if (JmlToken.IMPLIES.equals(token))
      res = Code.IMPLIES;
    if (JmlToken.EQUIVALENCE.equals(token))
      res = Code.EQUIV;
    if (res != -1) {
      return res;
    }
    throw new Jml2BmlException("Unrecognized token " + token);
  }

  /**
   * Creates new fieldRef for given index.
   * @param index index in the constant pool, where the field ref is being kept
   * @param symbols symbol table
   * @return created field ref.
   */
  public static FieldRef createFieldRef(final int index, final BCClass clazz) {
    return new FieldRef(clazz.getCp(), index);
  }

}
