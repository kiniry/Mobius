package jml2bml.bmllib;

import java.util.LinkedList;
import java.util.List;

import jml2bml.bytecode.TypeSignature;
import jml2bml.exceptions.Jml2BmlException;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.FieldOrMethod;

import annot.bcclass.BCClass;
import annot.bcclass.BCConstantPool;
import annot.bcclass.BCField;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;

/*
 * Manipulations on the BCConstantPool. Finding the corresponding
 * ConstantFieldRef and extending the constant pool, when necessary
 * (<code>object.field</code> accesses in JML that are not present in java
 * code). This should be done in the BmlLib.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0.0-1
 */
public final class ConstantPoolHelper {

  /**
   * Hidden constructor.
   */
  private ConstantPoolHelper() {
  }

  /**
   * Extends the constant pool (of the class taken from symbols),
   * so that the fieldref <code>object.field</code> can be resolved.
   * @param className - class of <code>object</code>
   * @param fieldName - name of <code>field</code>
   * @param symbols - symbol table (to find the current BCClass)
   * @param symbol - type symbol of <code>field</code>
   */
  public static void extendConstantPool(final Type type,
                                        final String fieldName,
                                        final BCClass clazz, 
                                        final Symbol symbol) {
    final BCConstantPool cp = clazz.getCp();
    final String fieldType = TypeSignature.getSignature(symbol.type);

    final int fieldTypeIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(fieldType));
    final int fieldNameIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(fieldName));
    final int classNameIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(trimClassName(TypeSignature.getSignature(type))));
    final int classIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantClass(classNameIndex));
    final int nameAndTypeIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantNameAndType(fieldNameIndex, fieldTypeIndex));
    cp.addConstant(new ConstantFieldref(classIndex, nameAndTypeIndex), true,
                   null);
  }

  /**
   * Finds the corresponding ConstantFieldRef for given className and
   * field (for <code>object.field</code>).
   * @param className - class name of the <code> object</code>
   * @param field - <code> field </code>
   * @param symbols - symbol table (to find the corresponding BCClass)
   * @return the index in the constantPool, or -1, when no entry found.
   */
  public static int findFieldInConstantPool(final String className, final FieldOrMethod field,
                                            final BCClass clazz) {
    final BCConstantPool cp = clazz.getCp();
    
    final String trimmedClassName = className.substring(1, className.lastIndexOf(";"));
    
    final int classNameIndex = cp.findConstant(trimmedClassName);
    final int classIndex = getConstantClassForNameIndex(classNameIndex, cp);
    
    
    final int nameAndTypeIndex = cp.findNATConstant(field.getNameIndex(), field.getSignatureIndex());
    return getConstantFieldRefForClassAndNameAndType(classIndex, nameAndTypeIndex, cp);
  }

  /**
   * Searches the constant pool for ConstantClass corresponding
   * to given classNameIndex.
   * @param classNameIndex - index of the class name in the constant pool
   * @param cp - constant pool
   * @return - index of the appropriate ConstantClass, or -1, when not found
   */
  private static int getConstantClassForNameIndex(final int classNameIndex,
                                                  final BCConstantPool cp) {
    final int size = cp.getSize();
    for (int i = 0; i < size; i++) {
      final Constant c = cp.getConstant(i);
      if (c instanceof ConstantClass) {
        if (((ConstantClass) c).getNameIndex() == classNameIndex) {
          return i;
        }
      }
    }
    //should never happen
    return -1;
  }

  /**
   * Finds the ConstantFieldref for given classIndex and nameAndTypeindex.
   * @param classIndex index in the constant pool of a ConstantClass
   * @param nameAndTypeindex index in the constant pool of a ConstantNameAndType
   * @param cp constant pool
   * @return index of the ConstantFieldref, or -1.
   */
  private static int getConstantFieldRefForClassAndNameAndType(
                                                               final int classIndex,
                                                               final int nameAndTypeindex,
                                                               final BCConstantPool cp) {
    final int size = cp.getSize();
    for (int i = 0; i < size; i++) {
      final Constant c = cp.getConstant(i);
      if (c instanceof ConstantFieldref) {
        final ConstantFieldref cfr = (ConstantFieldref) c;
        if (cfr.getClassIndex() == classIndex &&
            cfr.getNameAndTypeIndex() == nameAndTypeindex) {
          return i;
        }
      }
    }
    return -1;
  }

  /**
   * Tries to insert the given Constant to the constant pool.
   * If there exists already one with the same value,
   * the new constant will not be inserted.
   * @param cp - the constant pool
   * @param constant - inserted constant
   * @return - index of the newly inserted constant
   * (or of the old with the same value)
   */
  private static int tryInsert(final BCConstantPool cp,
                               final ConstantUtf8 constant) {
    final String key = constant.getBytes();
    final int index = cp.findConstant(key);
    if (index != -1) {
      return index;
    }
    cp.addConstant(constant, true, null);
    return cp.findConstant(key);
  }

  /**
   * Tries to insert the given Constant to the constant pool.
   * If there exists already one with the same value,
   * the new constant will not be inserted.
   * @param cp - the constant pool
   * @param cl - inserted constant
   * @return - index of the newly inserted constant
   * (or of the old with the same value)
   */
  private static int tryInsert(final BCConstantPool cp, final ConstantClass cl) {
    for (int i = 0; i < cp.getSize(); i++) {
      if (cp.getConstant(i) instanceof ConstantClass) {
        final ConstantClass tmp = (ConstantClass) cp.getConstant(i);
        if (tmp.getNameIndex() == cl.getNameIndex()) {
          return i;
        }
      }
    }
    cp.addConstant(cl, true, null);
    String clname = ((ConstantUtf8) cp.getConstant(cl.getNameIndex())).getBytes().replace('.', '/');
    for (int i = cp.getSize() - 1; i >= 0; i--) {
      if (cp.getConstant(i) instanceof ConstantClass) {
        final ConstantClass tmp = (ConstantClass) cp.getConstant(i);
        String tmpname = ((ConstantUtf8) cp.getConstant(tmp.getNameIndex())).getBytes();
        if (tmp.getNameIndex() == cl.getNameIndex()  ||
            tmpname.equals(clname)) {
          return i;
        }
      }
    }
    //should never happen!!!
    throw new Jml2BmlException("Serious error in constant pool "
                               + "- already inserted constant not found.");
  }

  /**
   * Tries to insert the given Constant to the constant pool.
   * If there exists already one with the same values,
   * the new constant will not be inserted.
   * @param cp - the constant pool
   * @param cnt - inserted constant
   * @return - index of the newly inserted constant
   * (or of the old with the same values)
   */
  private static int tryInsert(final BCConstantPool cp,
                               final ConstantNameAndType cnt) {
    for (int i = 0; i < cp.getSize(); i++) {
      if (cp.getConstant(i) instanceof ConstantNameAndType) {
        final ConstantNameAndType tmp = (ConstantNameAndType) cp.getConstant(i);
        if ((tmp.getNameIndex() == cnt.getNameIndex()) &&
            (tmp.getSignatureIndex() == cnt.getSignatureIndex())) {
          return i;
        }
      }
    }
    cp.addConstant(cnt, true, null);
    for (int i = cp.getSize() - 1; i >= 0; i--) {
      if (cp.getConstant(i) instanceof ConstantNameAndType) {
        final ConstantNameAndType tmp = (ConstantNameAndType) cp.getConstant(i);
        if ((tmp.getNameIndex() == cnt.getNameIndex()) &&
            (tmp.getSignatureIndex() == cnt.getSignatureIndex())) {
          return i;
        }
      }
    }
    //should never happen!!!
    throw new Jml2BmlException("Serious error in constant pool "
                               + "- already inserted constant not found.");

  }

  public static void addGhostField(final Type fieldType,
                                   final String fieldName, final BCClass clazz) {
    final BCConstantPool cp = clazz.getCp();
    final String className = clazz.getBCELClass().getClassName().replace('.', '/');
    final int fieldTypeIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(TypeSignature.getSignature(fieldType)));
    final int fieldNameIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(fieldName));
    final int classNameIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(className));
    final int classIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantClass(classNameIndex));
    final int nameAndTypeIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantNameAndType(fieldNameIndex, fieldTypeIndex));
    cp.addConstant(new ConstantFieldref(classIndex, nameAndTypeIndex), true,
                   null);
    final BCField afield = new BCField(clazz);
    afield.setNameIndex(fieldNameIndex);
    afield.setSignatureIndex(fieldTypeIndex);
    afield.setBMLKind(BCField.GHOST_FIELD);
    clazz.addGhostField(afield);
    System.err.println(cp.printCode(new StringBuffer()));
  }
  
  private static String trimClassName(String className){
    if (className.endsWith(";"))
      return className.substring(1, className.lastIndexOf(";"));
    return className;    
  }
}
