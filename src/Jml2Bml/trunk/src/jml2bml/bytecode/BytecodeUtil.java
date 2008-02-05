/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bytecode;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import jml2bml.exceptions.Jml2BmlException;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.verifier.structurals.ControlFlowGraph;
import org.apache.bcel.verifier.structurals.InstructionContext;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldRef;
import annot.io.ReadAttributeException;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 * @author Jedrek (fulara@mimuw.edu.pl)
 *
 * @version 0.0-1
 */
public final class BytecodeUtil {
  /**
   * Inner classes counter. I think it should be done in another way.
   */
  private static int innerClassNum = 1;

  /**
   * Hidden constructor.
   */
  private BytecodeUtil() {
  }

  /**
   * Searches for method of given name in given class.
   * @param name name of the method
   * @param clazz BCClass object representing the class
   * @return BCMethod representing method <code>name</code>,
   * or null, if the method was not found.
   */
  public static BCMethod findMethod(final CharSequence name, final BCClass clazz) {
    for (int i = 0; i < clazz.getMethodCount(); i++) {
      final BCMethod method = clazz.getMethod(i);
      //only for tests, to remove in the future
      LoopDetector.detectLoop(method);
      if (method.getBcelMethod().getName().contentEquals(name))
        return method;
    }
    return null;
  }

  /**
   * Creates FieldRef object for given field name in given class.
   * It is assumed that the field exists in this class. In the other case
   * an exception will be thrown.
   * @param isOld - if the reference occurs in \old clause
   * @param name - name of the field
   * @param clazz - class containing the field
   * @return FieldRef object.
   */
  public static BCExpression createFieldRef(final boolean isOld,
                                            final String name,
                                            final BCClass clazz) {
    final int nameIndex = clazz.getFieldIndex(name);
    if (nameIndex == -1) {
      throw new Jml2BmlException("Field " + name +
                                 " does not exist in given class.");
    }
    return new FieldRef(isOld, clazz.getCp(), nameIndex);

  }

  /**
   * Creates BCClass object for class of given name.
   * @param name - class name
   * @param context - application context
   * @return BCClass corresponding to given class name
   */
  public static BCClass createClass(final Name name, final Context context) {
    //Really hacked!
    final ClassFileLocation loc = context.get(ClassFileLocation.class);
    String qName = loc.getClassQualifiedName();
    final String cName = qName.substring(qName.lastIndexOf(".") + 1);
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
    } catch (ClassNotFoundException e) {
      throw new Jml2BmlException("Class " + qName + " not found.");
    } catch (ReadAttributeException e) {
      throw new Jml2BmlException("Error while loading class " + qName + ".");
    }
  }

}
