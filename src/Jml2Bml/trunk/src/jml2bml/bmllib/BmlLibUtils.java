/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-08 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bmllib;

import javax.lang.model.type.TypeKind;

import jml2bml.exceptions.Jml2BmlException;
import jml2bml.symbols.Symbols;

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
    case Code.EQUIV :
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

  private static int booleanOperator(final Kind kind) {
    if (kind == Kind.AND) {
      return Code.AND;
    }
    if (kind == Kind.EQUAL_TO) {
      return Code.EQ;
    }
    if (kind == Kind.GREATER_THAN) {
      return Code.GRT;
    }
    if (kind == Kind.GREATER_THAN_EQUAL) {
      return Code.GRTEQ;
    }
    if (kind == Kind.LEFT_SHIFT) {
      return Code.SHL;
    }
    if (kind == Kind.LESS_THAN) {
      return Code.LESS;
    }
    if (kind == Kind.LESS_THAN_EQUAL) {
      return Code.LESSEQ;
    }
    if (kind == Kind.NOT_EQUAL_TO) {
      return Code.NOTEQ;
    }
    if (kind == Kind.OR) {
      return Code.OR;
    }
    if (kind == Kind.CONDITIONAL_AND) {
      return Code.AND;
    }
    if (kind == Kind.CONDITIONAL_OR) {
      return Code.OR;
    }
    return -1;
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
    if (JmlToken.EQUIVALENCE.equals(token))
      return Code.EQUIV;

    throw new Jml2BmlException("Unrecognized token " + token);
  }
  public static FieldRef createFieldRef(boolean isOld, int index,
                                        Symbols symbols) {
    BCClass clazz = symbols.findClass();
    return new FieldRef(isOld, clazz.getCp(), index);
  }
  
}
