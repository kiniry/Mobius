/*
 * @title       "Jml2Bml"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.bytecode;

import javax.lang.model.element.Name;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 *
 */
public final class BytecodeUtil {
  private BytecodeUtil() {
  }

  public static BCMethod findMethod(final Name name, final BCClass clazz) {
    for (int i = 0; i < clazz.getMethodCount(); i++) {
      final BCMethod method = clazz.getMethod(i);
      if (name.contentEquals(method.getBcelMethod().getName()))
        return method;
    }
    return null;
  }
}
