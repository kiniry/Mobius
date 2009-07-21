/*
 * @title       "Jml2Bml" 
 * @description "JML to BML Compiler" 
 * @copyright   "(c) 2008-01-07 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.bytecode;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import jml2bml.bmllib.ConstantPoolHelper;
import jml2bml.exceptions.Jml2BmlException;
import jml2bml.exceptions.NotTranslatedRuntimeException;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantValue;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.FieldOrMethod;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
import org.apache.bcel.generic.Type;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;

import annot.bcclass.BCClass;
import annot.bcclass.BCField;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldRef;
import annot.bcexpression.NumberLiteral;

import com.sun.source.tree.LineMap;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;

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
      boolean direct = true;
      for(int j = 0; j < types.length; j++) {
        Type bytecodeType = types[j];
        JCTree sourceType = parameters.get(j).getType();
        if (bytecodeType instanceof BasicType) {
          ok = (sourceType.getKind() == Kind.PRIMITIVE_TYPE) && ((BasicType) bytecodeType).toString().equals(sourceType.toString());
        } else {
          if (sourceType.getKind() == Kind.PRIMITIVE_TYPE){
            ok = false;
          } else {
            String sourceTypeName = sourceType.toString();
            String bytecodeTypeName = bytecodeType.toString();
            
            if (!sourceTypeName.equals(bytecodeTypeName)){
              direct = false;
              if (!sourceTypeName.equals(bytecodeTypeName.substring(bytecodeTypeName.lastIndexOf('.')+1))){
                ok = false;
              }
            }
          }
          if (!ok) break;
        }
      }
      if (direct)
        return method;
      if (ok)
        candidates.add(method);
    }
    if (candidates.size() != 1){
      String errMsg;
      if (candidates.size() == 0)
        errMsg = "No matching candidate for method " + name + ": ";
      else
        errMsg = "Multiple candidates for method " + name + ": ";
      for (BCMethod met : candidates){
        errMsg += met.getBcelMethod().getSignature() +" ";
      }
      throw new Jml2BmlException(errMsg);
    }
    return candidates.get(0);
  }
  
  /**
   * Creates FieldRef object for given field name in given class.
   * It is assumed that the field exists in this class. In the other case
   * an exception will be thrown.
   * @param var - field variable
   * @param symbols - symbol table
   * @return FieldRef object.
   */
  public static BCExpression createFieldRef(final Symbol var,
                                            final BCClass clazz) {
    String className = clazz.getBCELClass().getClassName();
    className = "L" + className.replace('.', '/') + ";";
    final FieldOrMethod field = findField(clazz, var.name.toString());
    ConstantValue constantValue = null;
    if (field instanceof Field) {
      constantValue = ((Field)field).getConstantValue();
    } else {
      constantValue = ((BCField)field).getConstantValue();
    }
    if (constantValue==null) {
      return new FieldRef(clazz.getCp(), ConstantPoolHelper.findFieldInConstantPool(className, field, clazz));
    } else {
      final Constant constant = constantValue.getConstantPool().getConstant(constantValue.getConstantValueIndex());
      if (constant instanceof ConstantInteger) {
        ConstantInteger constantInt = (ConstantInteger) constant;
        return new NumberLiteral(constantInt.getBytes());
      }
      throw new NotTranslatedRuntimeException("Not translated constant type: "+var+":"+constantValue);
    }      
  }

//  /**
//   * Creates BCClass object for class of given name.
//   * Inner classes are NOT supported
//   * @param name - class name.
//   * @param context - application context
//   * @return BCClass corresponding to given class name
//   */
//  public static BCClass createClass(final Name name, final Context context) {
//    //Really hacked!
//    final ClassFileLocation loc = context.get(ClassFileLocation.class);
//    final String qName = loc.getClassQualifiedName();
//    try {
//      return new BCClass(loc.getDirectoryName(), qName);
//    } catch (ClassNotFoundException e) {
//      throw new Jml2BmlException("Class " + qName + " not found.");
//    } catch (ReadAttributeException e) {
//      throw new Jml2BmlException("Error while loading class " + qName + ".");
//    }
//  }

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
  
  public static FieldOrMethod findField(BCClass cl, String name){
    for (Field field : cl.getBCELClass().getFields()){
      if (name.equals(field.getName()))
          return field;
    }
    // ghost fields
    for (final Iterator <BCField> i = cl.getGhostFields().iterator();
         i.hasNext();) {
      final BCField field = i.next();
      if (name.equals(field.getName()))
          return field;
    }
    // model fields
    for (final Iterator <BCField> i = cl.getModelFields().iterator();
         i.hasNext();) {
      final BCField field = i.next();
      if (name.equals(field.getName()))
          return field;
    }
    return null;
  }
}
