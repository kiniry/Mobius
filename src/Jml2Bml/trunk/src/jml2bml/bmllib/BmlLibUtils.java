/*
 * @title       "Jml2Bml"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2008-01-08 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.bmllib;

import annot.io.Code;

import com.sun.source.tree.Tree.Kind;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 *
 */
public class BmlLibUtils {
  private BmlLibUtils() {}

  public static boolean isBinaryOperatorPredicate2Ar(int operator){
    switch(operator){
      case Code.GRT:
      case Code.GRTEQ:
      case Code.LESS:
      case Code.LESSEQ:
      case Code.EQ:
      case Code.NOTEQ:
        return true;
      default:
        return false;
    }
  }
  
  public static int translateBinaryOperator(Kind kind) {
    //TODO: check if all translated ok
    if (kind == Kind.AND) return Code.AND;
//    if (kind == Kind.CONDITIONAL_AND) return
//    if (kind == Kind.CONDITIONAL_OR) return
    if (kind == Kind.DIVIDE) return Code.DIV;
    if (kind == Kind.EQUAL_TO) return Code.EQ;
    if (kind == Kind.GREATER_THAN) return Code.GRT;
    if (kind == Kind.GREATER_THAN_EQUAL) return Code.GRTEQ;
    if (kind == Kind.LEFT_SHIFT) return Code.SHL;
    if (kind == Kind.LESS_THAN) return Code.LESS;
    if (kind == Kind.LESS_THAN_EQUAL) return Code.LESSEQ;
    if (kind == Kind.MINUS) return Code.MINUS;
    if (kind == Kind.MULTIPLY) return Code.MULT;
    if (kind == Kind.NOT_EQUAL_TO) return Code.NOTEQ;
    if (kind == Kind.OR) return Code.OR;
    if (kind == Kind.PLUS) return Code.PLUS;
    if (kind == Kind.REMAINDER) return Code.REM;
    if (kind == Kind.RIGHT_SHIFT) return Code.SHR;
//    if (kind == Kind.UNSIGNED_RIGHT_SHIFT) return
//    if (kind == Kind.XOR) return 
    throw new RuntimeException("Not implemented binary operator: " + kind);
  }

}
