/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-02-11 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.utils;

import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import com.sun.source.tree.ExpressionTree;

public final class JCUtils {
  public static boolean isOld(ExpressionTree node){
    if ("\\old".equals(node.toString())){
    return true;
    }
    return false;
  }
  public static boolean isPre(ExpressionTree node){
    if ("\\pre".equals(node.toString())){
      return true;
      }
      return false;
    }
  public static boolean isResult(JmlSingleton node) {
    if ("BSRESULT".equals(node.token.name())){
      return true;
    }
    return false;
  }
}
