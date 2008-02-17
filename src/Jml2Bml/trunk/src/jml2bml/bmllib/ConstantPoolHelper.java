package jml2bml.bmllib;

import java.util.LinkedList;
import java.util.List;

import jml2bml.exceptions.Jml2BmlException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.SyntheticRepository;

import annot.bcclass.BCClass;
import annot.bcclass.BCConstantPool;

/**
 * Manipulations on the BCConstantPool. Finding the corresponding
 * ConstantFieldRef and extending the constant pool,
 * when necessary (<code>object.field</code> accesses
 * in JML that are not present in java code). This should be done in the BmlLib.
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
   * Finds the type of <code>field</code> in class <code>className</code>.
   * @param className name of the class.
   * @param fieldName name of the field.
   * @return type of the field. If this field cannot be found in given class,
   * null will be returned.
   */
  private static String findFieldType(final String className,
                                      final String fieldName) {
    try {
      final JavaClass jc = SyntheticRepository.getInstance()
          .loadClass(className);
      final Field[] fields = jc.getFields();
      for (int i = 0; i < fields.length; i++) {
        if (fields[i].getName().equals(fieldName)) {
          return fields[i].getSignature();
        }
      }

    } catch (ClassNotFoundException e) {
      throw new Jml2BmlException("Class " + className + " not found.");
    }
    return null;
  }

  /**
   * Extends the constant pool (of the class taken from symbols),
   * so that the fieldref <code>object.field</code> can be resolved.
   * @param className - class of <code>object</code>
   * @param fieldName - name of <code>field</code>
   * @param symbols - symbol table (to find the current BCClass)
   */
  public static void extendConstantPool(final String className,
                                        final String fieldName,
                                        final Symbols symbols) {
    final String trimmedClassName = className.substring(1, className
        .lastIndexOf(";"));
    final String fieldType = findFieldType(trimmedClassName, fieldName);

    if (fieldType == null) {
      throw new Jml2BmlException("Field " + fieldName + " not found in class " +
                                 className + ".");
    }
    final BCClass clazz = symbols.findClass();
    final BCConstantPool cp = clazz.getCp();
    final int fieldTypeIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(fieldType));
    final int fieldNameIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(fieldName));
    final int classNameIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantUtf8(trimmedClassName));
    final int classIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantClass(classNameIndex));
    final int nameAndTypeIndex = ConstantPoolHelper
        .tryInsert(cp, new ConstantNameAndType(fieldNameIndex, fieldTypeIndex));
    cp.addConstant(new ConstantFieldref(classIndex, nameAndTypeIndex));
  }

  /**
   * Finds the corresponding ConstantFieldRef for given className and
   * fieldName (for <code>object.field</code>).
   * @param className - class name of the <code> object</code>
   * @param fieldName - name of the <code> field </code>
   * @param symbols - symbol table (to find the corresponding BCClass)
   * @return the index in the constantPool, or -1, when no entry found.
   */
  public static int findFieldInConstantPool(final String className,
                                            final String fieldName,
                                            final Symbols symbols) {
    final BCClass clazz = symbols.findClass();
    final BCConstantPool cp = clazz.getCp();
    //a little bit hacked: the className is Lpackage/name;
    //we want only package/name
    final String trimmedClassName = className.substring(1, className
        .lastIndexOf(";"));
    final int fieldNameIndex = cp.findConstant(fieldName);
    final int classNameIndex = cp.findConstant(trimmedClassName);
    final int classIndex = getConstantClassForNameIndex(classNameIndex, cp);
    final List<Integer> nameAndTypeIndexes =
      getConstantNameAndTypeForNameIndex(fieldNameIndex, cp);
    for (Integer nameAndTypeIndex : nameAndTypeIndexes) {
      final int constantFieldrefIndex =
        getConstantFieldRefForClassAndNameAndType(classIndex, nameAndTypeIndex,
                                                  cp);
      if (constantFieldrefIndex != -1) {
        return constantFieldrefIndex;
      }

    }
    return -1;
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
    final int size = cp.size();
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
   * Searches the given constant pool for ConstantNameAndType
   * for given nameIndex.
   * @param nameIndex index of the (field) name
   * @param cp constant pool
   * @return List of indexes of the ConstantNameAndTypes
   */
  private static List<Integer> getConstantNameAndTypeForNameIndex(final int nameIndex,
                                                                  final BCConstantPool cp) {
    final int size = cp.size();
    final List<Integer> res = new LinkedList<Integer>();
    for (int i = 0; i < size; i++) {
      final Constant c = cp.getConstant(i);
      if (c instanceof ConstantNameAndType) {
        if (((ConstantNameAndType) c).getNameIndex() == nameIndex) {
          res.add(i);
        }
      }
    }
    return res;
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
    final int size = cp.size();
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
    cp.addConstant(constant);
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
  private static int tryInsert(final BCConstantPool cp,
                               final ConstantClass cl) {
    for (int i = 0; i < cp.size(); i++) {
      if (cp.getConstant(i) instanceof ConstantClass) {
        final ConstantClass tmp = (ConstantClass) cp.getConstant(i);
        if (tmp.getNameIndex() == cl.getNameIndex()) {
          return i;
        }
      }
    }
    cp.addConstant(cl);
    for (int i = cp.size() - 1; i >= 0; i--) {
      if (cp.getConstant(i) instanceof ConstantClass) {
        final ConstantClass tmp = (ConstantClass) cp.getConstant(i);
        if (tmp.getNameIndex() == cl.getNameIndex()) {
          return i;
        }
      }
    }
    //should never happen!!!
    throw new Jml2BmlException("Serious error in constant pool " +
                               "- already inserted constant not found.");
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
    for (int i = 0; i < cp.size(); i++) {
      if (cp.getConstant(i) instanceof ConstantNameAndType) {
        final ConstantNameAndType tmp = (ConstantNameAndType) cp.getConstant(i);
        if ((tmp.getNameIndex() == cnt.getNameIndex()) &&
            (tmp.getSignatureIndex() == cnt.getSignatureIndex())) {
          return i;
        }
      }
    }
    cp.addConstant(cnt);
    for (int i = cp.size() - 1; i >= 0; i--) {
      if (cp.getConstant(i) instanceof ConstantNameAndType) {
        final ConstantNameAndType tmp = (ConstantNameAndType) cp.getConstant(i);
        if ((tmp.getNameIndex() == cnt.getNameIndex()) &&
            (tmp.getSignatureIndex() == cnt.getSignatureIndex())) {
          return i;
        }
      }
    }
    //should never happen!!!
    throw new Jml2BmlException("Serious error in constant pool " +
                               "- already inserted constant not found.");

  }

}
