/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-07 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.bytecode;

import java.util.HashMap;
import java.util.Map;

import jml2bml.bmllib.ConstantPoolHelper;
import jml2bml.exceptions.Jml2BmlException;
import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldRef;
import annot.io.ReadAttributeException;

import com.sun.source.tree.LineMap;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.tree.JCTree;
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
   * @param symbols - symbol table
   * @return FieldRef object.
   */
  public static BCExpression createFieldRef(final boolean isOld,
                                            final String name,
                                            final Symbols symbols) {
    final BCClass clazz = symbols.findClass();
    String className = clazz.getJC().getClassName();
    className = "L" + className.replace('.', '/') + ";";
    final int nameIndex = ConstantPoolHelper.findFieldInConstantPool(className,
                                                                     name,
                                                                     symbols);
    if (nameIndex == -1) {
      throw new Jml2BmlException("Field " + name
                                 + " does not exist in given class.");
    }
    return new FieldRef(isOld, clazz.getCp(), nameIndex);

  }

  /**
   * Creates BCClass object for class of given name.
   * Inner classes are NOT supported
   * @param name - class name.
   * @param context - application context
   * @return BCClass corresponding to given class name
   */
  public static BCClass createClass(final Name name, final Context context) {
    //Really hacked!
    final ClassFileLocation loc = context.get(ClassFileLocation.class);
    final String qName = loc.getClassQualifiedName();
    try {
      return new BCClass(loc.getDirectoryName(), qName);
    } catch (ClassNotFoundException e) {
      throw new Jml2BmlException("Class " + qName + " not found.");
    } catch (ReadAttributeException e) {
      throw new Jml2BmlException("Error while loading class " + qName + ".");
    }
  }

  /**
   * Finds the line number for given node in given LineMap.
   * @param node - node, for which the line number should be found
   * @param lineMap line map containing line numbers for positions
   * in the file
   * @return line number of <code>node</code>
   */
  public static long getLineNumber(final Tree node, final LineMap lineMap) {
    return lineMap.getLineNumber(((JCTree) node).getStartPosition());
  }

  /**
   * Returns map: bytecode instruction -> line number in the source file.
   * @param method - method, for which the map should be generated
   * @return map: <code>Bytecode Instruction -> line in the source code</code>
   * @throws NotTranslatedRuntimeException 
   */
  public static Map<InstructionHandle, Integer> getLineNumberMap(
                                                                 final BCMethod method) throws NotTranslatedRuntimeException {
    final Map<InstructionHandle, Integer> result = new HashMap<InstructionHandle, Integer>();
    for (LineNumberGen lng : method.getBcelMethod().getLineNumbers())
      if (result.containsKey(lng.getInstruction()))
        throw new NotTranslatedRuntimeException(
                                         "One bytecode instruction has more than one line number");
      else
        result.put(lng.getInstruction(), lng.getSourceLine());
    return result;
  }
}
