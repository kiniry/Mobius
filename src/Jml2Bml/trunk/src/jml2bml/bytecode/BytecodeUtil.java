/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bytecode;


import jml2bml.engine.Symbols;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldRef;

import com.sun.tools.javac.util.Context;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 *
 */
public final class BytecodeUtil {
  private static int innerClassNum = 1;
  private BytecodeUtil() {
  }

  public static BCMethod findMethod(final CharSequence name, final BCClass clazz) {
    for (int i = 0; i < clazz.getMethodCount(); i++) {
      final BCMethod method = clazz.getMethod(i);
      if (method.getBcelMethod().getName().contentEquals(name))
        return method;
    }
    return null;
  }

  public static BCExpression createFieldRef(boolean isOld, String name,
                                            BCClass clazz) {
    int nameIndex = clazz.getFieldIndex(name);
    if (nameIndex == -1) {
      //FIXME throw an exception
    }
    return new FieldRef(isOld, clazz.getCp(), nameIndex);

  }

  public static BCClass createClass(com.sun.tools.javac.util.Name name,
                                    Context context, Symbols symbols) {
    //Really hacked!
    ClassFileLocation loc = context.get(ClassFileLocation.class);
    String qName = loc.getClassQualifiedName();
    String cName = qName.substring(qName.lastIndexOf(".") + 1);
    if (!cName.equals(name.toString())) {
      if (name.toString().length() == 0) {
        qName += "$" + innerClassNum;
        innerClassNum++;
      } else {
        qName += "$" + name.toString();
      }
    }
    try {
      return new BCClass(loc.getDirectoryName(), qName);
    } catch (Exception e) {
      //FIXME handle the exception!!
      System.out.println(e);
      return null;
    }
  }
}
