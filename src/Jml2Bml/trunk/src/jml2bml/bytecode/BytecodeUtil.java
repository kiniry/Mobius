/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-07 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bytecode;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import jml2bml.bmllib.ConstantPoolHelper;
import jml2bml.exceptions.Jml2BmlException;
import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
import org.apache.bcel.generic.Type;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldRef;
import annot.io.ReadAttributeException;

import com.sun.source.tree.LineMap;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
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
   * @param sourceMethod source method object
   * @param clazz BCClass object representing the class
   * @return BCMethod representing method <code>name</code>,
   * or null, if the method was not found.
   */
  public static BCMethod findMethod(final JmlMethodDecl sourceMethod,
                                    final BCClass clazz) {
    final CharSequence name = sourceMethod.getName();
    final List<JCVariableDecl> parameters = sourceMethod.getParameters();
    List<BCMethod> candidates = new LinkedList < BCMethod >();
    for (int i = 0; i < clazz.getMethodCount(); i++) {
      final BCMethod method = clazz.getMethod(i);
      if (!method.getBcelMethod().getName().contentEquals(name))
        continue;
      Type[] types = method.getBcelMethod().getArgumentTypes();
      
      if (types.length != parameters.size())
        continue;
      boolean ok = true;
      for(int j = 0; j < types.length; j++) {
        Type bytecodeType = types[j];
        JCTree parameterType = parameters.get(j).getType();
        String sourceTypeName = null;
        if (parameterType.getKind() == Kind.PRIMITIVE_TYPE){
           sourceTypeName = parameterType.toString();
        } else if (parameterType.getKind() == Kind.IDENTIFIER) {
          sourceTypeName = ((JCIdent) parameterType).sym.toString();          
        } else
          throw new RuntimeException("Unknown type kind: "+ parameterType + ":" + parameterType.getKind());
        if (!sourceTypeName.contentEquals(bytecodeType.toString())){
          ok = false;
          break;
        }
      }
      if (ok)
        candidates.add(method);
    }
    if (candidates.size() != 1){
      String errMsg = "Multiple candidates for method " + name + ": ";
      for (BCMethod met : candidates){
        errMsg += met.getBcelMethod().getSignature() +" ";
      }
      throw new Jml2BmlException(errMsg);
    }
    return candidates.get(0);
  }
  
  /**
   * Searches for method of given name in given class.
   * @param name name of the method
   * @param clazz BCClass object representing the class
   * @return BCMethod representing method <code>name</code>,
   * or null, if the method was not found.
   */
  public static BCMethod findMethod(final CharSequence name, List<JCVariableDecl> parameters,
                                    final BCClass clazz) {
    List<BCMethod> candidates = new LinkedList < BCMethod >();
    for (int i = 0; i < clazz.getMethodCount(); i++) {
      final BCMethod method = clazz.getMethod(i);
      if (method.getBcelMethod().getName().contentEquals(name)){
        Type[] types = method.getBcelMethod().getArgumentTypes();
        
        if (types.length != parameters.size()){
          continue;
        }
        for (int j = 0; j < types.length; j++){
          String bcelTypeName = extractNameFromType(types[j]);
        
          if (bcelTypeName != parameters.get(j).vartype.toString()){
            continue;
          }
                    
        }
        candidates.add(method);
        return method;
      }
    }
    if (candidates.size() != 1){
      String errMsg = "Multiple candidates for method " + name + ": ";
      for (BCMethod met : candidates){
        errMsg += met.getBcelMethod().getSignature() +" ";
      }
      throw new Jml2BmlException(errMsg);
    }
    return candidates.get(0);
  }

  private static String extractNameFromType(Type type){
    if (type instanceof BasicType){
      return type.getSignature();
    }
    String[] splitted = type.getSignature().split("/");
    String lastPart = splitted[splitted.length - 1]; 
    return lastPart.substring(0, lastPart.length() - 1);
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
      throw new Jml2BmlException("Field " + name +
                                 " does not exist in given class.");
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
  public static Map < InstructionHandle, Integer > getLineNumberMap(
      final BCMethod method)
      throws NotTranslatedRuntimeException {
    final Map < InstructionHandle, Integer > result =
      new HashMap < InstructionHandle, Integer >();
    for (LineNumberGen lng : method.getBcelMethod().getLineNumbers())
      if (result.containsKey(lng.getInstruction()))
        throw new NotTranslatedRuntimeException(
          "One bytecode instruction has more than one line number");
      else
        result.put(lng.getInstruction(), lng.getSourceLine());
    return result;
  }
}
