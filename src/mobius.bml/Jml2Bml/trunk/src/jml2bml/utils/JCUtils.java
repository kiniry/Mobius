/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-02-11 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.utils;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import com.sun.tools.javac.tree.JCTree;

/**
 * Util class for manipulating JCTree nodes (checking if something is \old,
 * ghost, \result etc).
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0.0-1
 */
public final class JCUtils {
  /**
   * Hidden constructor.
   */
  private JCUtils() {

  }

  /**
   * Checks if the given JmlSingleton is \result.
   * @param node JmlSingleton to check
   * @return if the singleton is \result
   */
  public static boolean isResult(final JmlSingleton node) {
    return "BSRESULT".equals(node.token.name());
  }

  /**
   * Checks, if the variable declaration has modifier 'ghost'.
   * @param node variable declaration to check
   * @return if the variable is ghost
   */
  public static boolean isGhost(final JmlTree.JmlVariableDecl node) {
    if (node != null && node.mods != null && node.mods.annotations != null) {
      for (JCTree.JCAnnotation a : node.mods.annotations) {
        if (a.annotationType instanceof JCTree.JCFieldAccess) {
          if ("ghost"
              .equalsIgnoreCase(((JCTree.JCFieldAccess) a.annotationType).name
                  .toString())) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /**
   * Checks if the variable is a model variable.
   * @param node variable declaration to check
   * @return if the variable is declared 'model'
   */
  public static boolean isModal(final JmlTree.JmlVariableDecl node) {
    if (node != null && node.mods != null && node.mods.annotations != null) {
      for (JCTree.JCAnnotation a : node.mods.annotations) {
        if (a.annotationType instanceof JCTree.JCFieldAccess) {
          if ("modal"
              .equalsIgnoreCase(((JCTree.JCFieldAccess) a.annotationType).name
                  .toString())) {
            return true;
          }
        }
      }
    }
    return false;
  }
}
