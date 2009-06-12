/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantInterfaceMethodref;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.ConstantValue;
import org.apache.bcel.classfile.ExceptionTable;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.LineNumberTable;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.LocalVariableTable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.PMGClass;
import org.apache.bcel.classfile.Signature;
import org.apache.bcel.classfile.SourceFile;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;

import annot.bcclass.BCClass;

/**
 * This class generates dummy constant pool entries. The references to
 * non-existing constants or to incorrect constants are changed to point
 * to those dummy constants. This allows to save class with incorrect
 * constant pool to class file. <br> <br>
 *
 * TODO (Umbra) generate dummies for incorrect references from instructions
 * <br> <br>
 * TODO (Umbra) it should probably get information about malformed constant
 * pool from {@link umbra.instructions.errors.ErrorReport} instead of getting
 * it by itself.
 * <br> <br>
 * FIXME (Umbra) editing or removing of constants that are referenced by:
 * <ul>
 * <li> Attribute, especially:
 * <ul>
 * <li> LocalVariable
 * <li> ExceptionTable
 * </ul>
 * <li> Method
 * </ul>
 * cause exceptions when bytecode is reloaded from .class file after save
 * or refresh. This class tries to make constant pool consistent before
 * save to avoid that, however it does not work very well in such cases.
 * The editor probably should report an error if name/signature of method or
 * local variable or exception type in exception table has changed and add
 * constant with given name/signature/exception type to constnat pool if user
 * decides to save despite error.
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class DummyGenerator {

  /**
   * A class for which we check constant pool correctness and generate
   * dummy constants if necessary.
   */
  private JavaClass my_jc;

  /**
   * BML representation of checked class.
   */
  private BCClass my_bc;

  /**
   * That object stores various information. We use it to get names of
   * local variables when the constant pool is not consistent.
   */
  private BytecodeMapping my_mapping;

  /**
   * Index of dummy Class constant.
   */
  private int my_dummy_class_index;

  /**
   * Index of dummy Utf8 constant.
   */
  private int my_dummy_utf_index;

  /**
   * Index of dummy class name constant.
   */
  private int my_dummy_class_name_index;

  /**
   * Index of dummy Utf8 constant with "void ...()" singature.
   */
  private int my_dummy_sig_index;

  /**
   * Index of dummy Utf8 constant with "int" signature.
   */
  private int my_dummy_field_sig_index;

  /**
   * Index of dummy NameAndType constant for methods.
   */
  private int my_dummy_name_and_type_index;

  /**
   * Index of dummy NameAndType constant for fields.
   */
  private int my_dummy_name_and_type_index_for_fields;
  
  private int my_dummy_exception_index;
  private int my_dummy_exception_name_index;

  /**
   * Index of dummy Utf8 constants with standard java class attribute
   * names (Code, LocalVariableTable, etc.).
   */
  private HashMap < Class, Integer > my_dummy_utfs;

  /**
   * Temporary copy of constant pool.
   */
  private ArrayList < Constant > my_constants;

  /**
   *
   * @param classGen a class for which we check constant pool
   * correctness and generate dummy constants if necessary
   * @param a_bc BML representation of this class
   * @param a_mapping object from which we can get local variable names when
   * constant pool is not consistent
   */
  public DummyGenerator(final JavaClass classGen, final BCClass a_bc,
                        final BytecodeMapping a_mapping) {
    my_jc = classGen;
    my_bc = a_bc;
    my_mapping = a_mapping;
    my_dummy_utfs = new HashMap < Class, Integer > ();
  }

  /**
   * Generates dummy constant pool entries. The references to
   * non-existing constants or to incorrect constants are changed to point
   * to those dummy constants. This allows to save class with incorrect
   * constant pool to class file. <br> <br>
   * In some cases it can turn incorrect bytecode into correct one. <br>
   * These are the cases <br>
   * <ul>
   * <li> reference to non-existent/incorrect attribute name from attribute
   * <li> reference to non-existent/incorrect method signature from method
   * <li> reference to non-existent/incorrect local variable signature
   * from local variable
   * <li> reference to non-existent/incorrect local variable name
   * from local variable
   * </ul>
   */
  public void generateDummyConstants() {
    my_constants = new ArrayList < Constant > ();
    for (Constant c : my_jc.getConstantPool().
                            getConstantPool()) {
      my_constants.add(c);
    }
    initDummyUtfs();
    my_dummy_utf_index = -1;
    my_dummy_class_index = -1;
    my_dummy_name_and_type_index = -1;
    my_dummy_name_and_type_index_for_fields = -1;
    my_dummy_class_name_index = -1;
    my_dummy_sig_index = -1;
    my_dummy_field_sig_index = -1;
    my_dummy_exception_index = -1;
    my_dummy_exception_name_index = -1;
    final int length = my_jc.getConstantPool().getLength();
    for (int i = 0; i < length; i++) {
      final Constant c = my_jc.getConstantPool().getConstant(i);
      if (c instanceof ConstantClass) update((ConstantClass) c);
      else if (c instanceof ConstantFieldref)
        update((ConstantFieldref) c, false);
      else if (c instanceof ConstantMethodref)
        update((ConstantMethodref) c, false);
      else if (c instanceof ConstantInterfaceMethodref)
        update((ConstantInterfaceMethodref) c, false);
      else if (c instanceof ConstantNameAndType)
        update((ConstantNameAndType) c, i);
      else if (c instanceof ConstantString) update((ConstantString) c);
    }
    final List < Attribute > attrs = new ArrayList < Attribute > ();
    final List < LocalVariable > lvars = new ArrayList < LocalVariable > ();
    for (Field f : my_jc.getFields()) {
      update(f);
      for (Attribute a : f.getAttributes()) attrs.add(a);
    }
    for (int i = 0; i < my_jc.getMethods().length; i++) {
      update(my_jc.getMethods()[i],
             my_bc.getMethod(i).getBcelMethod().getSignature());
      for (Attribute a : my_jc.getMethods()[i].getAttributes()) {
        if (a instanceof Code) {
          final Code c = (Code) a;
          for (Attribute at : c.getAttributes()) {
            if (at instanceof LocalVariableTable) {
              final LocalVariableTable lvt = (LocalVariableTable) at;
              for (LocalVariable lv : lvt.getLocalVariableTable()) lvars.add(lv);
            }
            attrs.add(at);
          }
        }
        attrs.add(a);
      }
    }
    for (Attribute a : my_jc.getAttributes()) attrs.add(a);
    for (Attribute a : attrs) update(a);
    for (LocalVariable lv : lvars) update(lv);
    try {
      final Constant cni =
        my_jc.getConstantPool().getConstant(my_jc.getClassNameIndex());
      if (!(cni instanceof ConstantClass))
        my_jc.setClassNameIndex(getDummyClass());
    } catch (ClassFormatException e) {
      my_jc.setClassNameIndex(getDummyClass());
    }
    try {
      final Constant scni =
        my_jc.getConstantPool().getConstant(my_jc.getSuperclassNameIndex());
      if (!(scni instanceof ConstantClass))
        my_jc.setSuperclassNameIndex(getDummyClass());
    } catch (ClassFormatException e) {
      my_jc.setSuperclassNameIndex(getDummyClass());
    }
    final Constant[] cp = new Constant[my_constants.size()];
    int k = 0;
    for (Constant c : my_constants) {
      cp[k] = c;
      k++;
    }
    final ConstantPoolGen cpg = new ConstantPoolGen(my_jc.getConstantPool());
    for (Constant c : cp) {
      if (c != null) cpg.addConstant(c, cpg);
    }
    my_jc.getConstantPool().setConstantPool(cpg.getFinalConstantPool().
                                            getConstantPool());
  }

  /**
   *
   * @return dummy Utf8 constant index
   */
  private int getDummyUtf() {
    if (my_dummy_utf_index != -1) return my_dummy_utf_index;
    my_constants.add(new ConstantUtf8("dummy"));
    my_dummy_utf_index = my_constants.size() - 1;
    return my_dummy_utf_index;
  }

  /**
   * Creates new Utf8 constant.
   *
   * @param a_value value of the constant
   * @return index of the constant
   */
  private int getDummyUtf(final String a_value) {
    my_constants.add(new ConstantUtf8(a_value));
    return my_constants.size() - 1;
  }

  /**
   *
   * @return Utf8 constant index with dummy class name
   */
  private int getDummyClassName() {
    if (my_dummy_class_name_index != -1) return my_dummy_class_name_index;
    my_constants.add(new ConstantUtf8("java/lang/Object"));
    my_dummy_class_name_index = my_constants.size() - 1;
    return my_dummy_class_name_index;
  }

  /**
  *
  * @return dummy Class constant index
  */
  private int getDummyClass() {
    if (my_dummy_class_index != -1) return my_dummy_class_index;
    my_constants.add(new ConstantClass(getDummyClassName()));
    my_dummy_class_index = my_constants.size() - 1;
    return my_dummy_class_index;
  }

  /**
   *
   * @return dummy NameAndType constant index for methods
   */
  private int getDummyNameAndType() {
    if (my_dummy_name_and_type_index != -1) return my_dummy_name_and_type_index;
    my_constants.add(new ConstantNameAndType(getDummyUtf(), getDummySig()));
    my_dummy_name_and_type_index = my_constants.size() - 1;
    return my_dummy_name_and_type_index;
  }

  /**
   *
   * @return dummy NameAndType constant index for fields
   */
  private int getDummyNameAndTypeForFields() {
    if (my_dummy_name_and_type_index_for_fields != -1)
      return my_dummy_name_and_type_index_for_fields;
    my_constants.add(new ConstantNameAndType(getDummyUtf(),
                                             getDummyFieldSig()));
    my_dummy_name_and_type_index_for_fields = my_constants.size() - 1;
    return my_dummy_name_and_type_index_for_fields;
  }

  /**
   *
   * @return Utf8 constant index with "void ...()" signature
   */
  private int getDummySig() {
    if (my_dummy_sig_index != -1) return my_dummy_sig_index;
    my_constants.add(new ConstantUtf8("()V"));
    my_dummy_sig_index = my_constants.size() - 1;
    return my_dummy_sig_index;
  }

  /**
   *
   * @param a_sig method signature
   * @return Utf8 constant index with given signature
   */
  private int getDummySig(final String a_sig) {
    my_constants.add(new ConstantUtf8(a_sig));
    return my_constants.size() - 1;
  }

  /**
   *
   * @return Utf8 constant index with "int" signature
   */
  private int getDummyFieldSig() {
    if (my_dummy_field_sig_index != -1) return my_dummy_field_sig_index;
    my_constants.add(new ConstantUtf8("I"));
    my_dummy_field_sig_index = my_constants.size() - 1;
    return my_dummy_field_sig_index;
  }


  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_c a constant
   */
  private void update(final ConstantClass a_c) {
    try {
      final Constant name =
        my_jc.getConstantPool().getConstant(a_c.getNameIndex());
      if (!(name instanceof ConstantUtf8))
        a_c.setNameIndex(getDummyClassName());
    } catch (ClassFormatException e) {
      a_c.setNameIndex(getDummyClassName());
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_c a constant
   * @param a_nat_only check only name and type
   */
  private void update(final ConstantFieldref a_c, final boolean a_nat_only) {
    if (!a_nat_only) {
      try {
        final Constant a_class =
          my_jc.getConstantPool().getConstant(a_c.getClassIndex());
        if (!(a_class instanceof ConstantClass))
          a_c.setClassIndex(getDummyClass());
      } catch (ClassFormatException e) {
        a_c.setClassIndex(getDummyClass());
      }
    }
    try {
      final Constant nat =
        my_jc.getConstantPool().getConstant(a_c.getNameAndTypeIndex());
      if (!(nat instanceof ConstantNameAndType))
        a_c.setNameAndTypeIndex(getDummyNameAndTypeForFields());
    } catch (ClassFormatException e) {
      a_c.setNameAndTypeIndex(getDummyNameAndTypeForFields());
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_c a constant
   * @param a_nat_only check only name and type
   */
  private void update(final ConstantMethodref a_c, final boolean a_nat_only) {
    if (!a_nat_only) {
      try {
        final Constant a_class =
          my_jc.getConstantPool().getConstant(a_c.getClassIndex());
        if (!(a_class instanceof ConstantClass))
          a_c.setClassIndex(getDummyClass());
      } catch (ClassFormatException e) {
        a_c.setClassIndex(getDummyClass());
      }
    }
    try {
      final Constant nat =
        my_jc.getConstantPool().getConstant(a_c.getNameAndTypeIndex());
      if (!(nat instanceof ConstantNameAndType))
        a_c.setNameAndTypeIndex(getDummyNameAndType());
    } catch (ClassFormatException e) {
      a_c.setNameAndTypeIndex(getDummyNameAndType());
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_c a constant
   * @param a_nat_only check only name and type
   */
  private void update(final ConstantInterfaceMethodref a_c,
                      final boolean a_nat_only) {
    if (!a_nat_only) {
      try {
        final Constant a_class =
          my_jc.getConstantPool().getConstant(a_c.getClassIndex());
        if (!(a_class instanceof ConstantClass))
          a_c.setClassIndex(getDummyClass());
      } catch (ClassFormatException e) {
        a_c.setClassIndex(getDummyClass());
      }
    }
    try {
      final Constant nat =
        my_jc.getConstantPool().getConstant(a_c.getNameAndTypeIndex());
      if (!(nat instanceof ConstantNameAndType))
        a_c.setNameAndTypeIndex(getDummyNameAndType());
    } catch (ClassFormatException e) {
      a_c.setNameAndTypeIndex(getDummyNameAndType());
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_c a constant
   * @param an_index index of constant in constant pool
   */
  private void update(final ConstantNameAndType a_c, final int an_index) {
    try {
      final Constant name =
        my_jc.getConstantPool().getConstant(a_c.getNameIndex());
      if (!(name instanceof ConstantUtf8)) a_c.setNameIndex(getDummyUtf());
    } catch (ClassFormatException e) {
      a_c.setNameIndex(getDummyUtf());
    }
    final Class c = getReference(an_index);
    if (c == ConstantFieldref.class) {
      try {
        final Constant type =
          my_jc.getConstantPool().getConstant(a_c.getSignatureIndex());
        if (!(type instanceof ConstantUtf8))
          a_c.setSignatureIndex(getDummyFieldSig());
      } catch (ClassFormatException e) {
        a_c.setSignatureIndex(getDummyFieldSig());
      }
    } else {
      try {
        final Constant type =
          my_jc.getConstantPool().getConstant(a_c.getSignatureIndex());
        if (!(type instanceof ConstantUtf8))
          a_c.setSignatureIndex(getDummySig());
      } catch (ClassFormatException e) {
        a_c.setSignatureIndex(getDummySig());
      }
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_c a constant
   */
  private void update(final ConstantString a_c) {
    try {
      final Constant string =
        my_jc.getConstantPool().getConstant(a_c.getStringIndex());
      if (!(string instanceof ConstantUtf8)) a_c.setStringIndex(getDummyUtf());
    } catch (ClassFormatException e) {
      a_c.setStringIndex(getDummyUtf());
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_field a field
   */
  private void update(final Field a_field) {
    try {
      final Constant name =
        my_jc.getConstantPool().getConstant(a_field.getNameIndex());
      if (!(name instanceof ConstantUtf8))
        a_field.setNameIndex(getDummyUtf());
    } catch (ClassFormatException e) {
      a_field.setNameIndex(getDummyUtf());
    }
    try {
      final Constant sig =
        my_jc.getConstantPool().getConstant(a_field.getSignatureIndex());
      if (!(sig instanceof ConstantUtf8))
        a_field.setSignatureIndex(getDummyFieldSig());
    } catch (ClassFormatException e) {
      a_field.setSignatureIndex(getDummyFieldSig());
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_method a method
   * @param a_signature method signature
   */
  private void update(final Method a_method, final String a_signature) {
    try {
      final Constant name =
        my_jc.getConstantPool().getConstant(a_method.getNameIndex());
      if (!(name instanceof ConstantUtf8))
        a_method.setNameIndex(getDummyUtf());
    } catch (ClassFormatException e) {
      a_method.setNameIndex(getDummyUtf());
    }
    try {
      final Constant sig =
        my_jc.getConstantPool().getConstant(a_method.getSignatureIndex());
      if (!(sig instanceof ConstantUtf8))
        a_method.setSignatureIndex(getDummySig(a_signature));
    } catch (ClassFormatException e) {
      a_method.setSignatureIndex(getDummySig(a_signature));
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param an_attr a field
   */
  private void update(final Attribute an_attr) {
    try {
      if (!properNameConstant(an_attr))
        an_attr.setNameIndex(getDummyUtf(an_attr.getClass()));
    } catch (ClassFormatException e) {
      an_attr.setNameIndex(getDummyUtf(an_attr.getClass()));
    }
    if (an_attr instanceof SourceFile) {
      final SourceFile sc = (SourceFile) an_attr;
      try {
        final Constant cnst =
          my_jc.getConstantPool().getConstant(sc.getSourceFileIndex());
        if (!(cnst instanceof ConstantUtf8))
          sc.setSourceFileIndex(getDummyUtf());
      } catch (ClassFormatException e) {
        sc.setSourceFileIndex(getDummyUtf());
      }
    } else if (an_attr instanceof ConstantValue) {
      final ConstantValue cv = (ConstantValue) an_attr;
      try {
        final Constant cnst =
          my_jc.getConstantPool().getConstant(cv.getConstantValueIndex());
        if (!(cnst instanceof ConstantUtf8))
          cv.setConstantValueIndex(getDummyUtf());
      } catch (ClassFormatException e) {
        cv.setConstantValueIndex(getDummyUtf());
      }
    } else if (an_attr instanceof Signature) {
      final Signature sig = (Signature) an_attr;
      try {
        final Constant cnst =
          my_jc.getConstantPool().getConstant(sig.getSignatureIndex());
        if (!(cnst instanceof ConstantUtf8))
          sig.setSignatureIndex(getDummySig());
      } catch (ClassFormatException e) {
        sig.setSignatureIndex(getDummySig());
      }
    } else if (an_attr instanceof PMGClass) {
      final PMGClass pmg = (PMGClass) an_attr;
      try {
        final Constant cnst =
          my_jc.getConstantPool().getConstant(pmg.getPMGIndex());
        if (!(cnst instanceof ConstantUtf8))
          pmg.setPMGIndex(getDummyClassName());
      } catch (ClassFormatException e) {
        pmg.setPMGIndex(getDummyClassName());
      }
      try {
        final Constant cnst =
          my_jc.getConstantPool().getConstant(pmg.getPMGClassIndex());
        if (!(cnst instanceof ConstantUtf8))
          pmg.setPMGClassIndex(getDummyClassName());
      } catch (ClassFormatException e) {
        pmg.setPMGClassIndex(getDummyClassName());
      }
    } else if (an_attr instanceof ExceptionTable) {
      /* Note: references from exception tables should point to const Class,
       * not to const Utf8. However adding utf8 instead works too, and if that
       * happens bytecode is already incorrect.
       */
      final ExceptionTable et = (ExceptionTable) an_attr;
      for (int i = 0; i < et.getExceptionIndexTable().length; i++) {
        try {
          final Constant exc =
            my_jc.getConstantPool().getConstant(et.getExceptionIndexTable()[i]);
          if (!(exc instanceof ConstantClass))
              et.getExceptionIndexTable()[i] = getDummyException();
        } catch (ClassFormatException e) {
          et.getExceptionIndexTable()[i] = getDummyException();
        }
      }
    }
  }

  /**
   * Changes incorrect references in such way that they point to dummy
   * constants.
   *
   * @param a_lvar a local variable
   */
  private void update(final LocalVariable a_lvar) {
    try {
      final Constant name =
        my_jc.getConstantPool().getConstant(a_lvar.getNameIndex());
      if (!(name instanceof ConstantUtf8))
        a_lvar.setNameIndex(getDummyUtf(my_mapping.getLocVarName(a_lvar)));
    } catch (ClassFormatException e) {
      a_lvar.setNameIndex(getDummyUtf(my_mapping.getLocVarName(a_lvar)));
    }
    try {
      final Constant sig =
        my_jc.getConstantPool().getConstant(a_lvar.getSignatureIndex());
      if (!isFieldDescriptor(sig))
        a_lvar.
        setSignatureIndex(getDummyUtf(my_mapping.getLocVarSignature(a_lvar)));
    } catch (ClassFormatException e) {
      a_lvar.
      setSignatureIndex(getDummyUtf(my_mapping.getLocVarSignature(a_lvar)));
    }
  }

  /**
   * Returns the class of the first constant that point to the
   * name and type constant at index an_index. If other constants
   * that point to the name and type constant are in conflict with
   * this first constant they are set to point on dummy name and type.
   * <br> <br>
   * Two constants are in conflict if one of them is Fieldref (name
   * and type must point to field signature) and the other one is
   * Methodref or InterfaceMethodref (name and type must point to method
   * signature).
   *
   * @param an_index an index to name and type constant
   * @return class of the first constant that point to the name and type
   * constant 
   */
  private Class getReference(final int an_index) {
    Class res = null;
    final int max = my_jc.getConstantPool().getLength();
    for (int i = 0; i < my_jc.getConstantPool().getLength(); i++) {
      final Constant c = my_jc.getConstantPool().getConstant(i);
      if (c instanceof ConstantFieldref) {
        final ConstantFieldref cf = (ConstantFieldref) c;
        if (cf.getNameAndTypeIndex() == an_index) {
          if (res == null) {
            res = ConstantFieldref.class;
          } else if (res != ConstantFieldref.class) {
            cf.setNameAndTypeIndex(max + 1);
            if (i < an_index) update(cf, true);
          }
        }
      } else if (c instanceof ConstantMethodref) {
        final ConstantMethodref cm = (ConstantMethodref) c;
        if (cm.getNameAndTypeIndex() == an_index) {
          if (res == null) {
            res = ConstantMethodref.class;
          } else if (res == ConstantFieldref.class) {
            cm.setNameAndTypeIndex(max + 1);
            if (i < an_index) update(cm, true);
          }
        }
      } else if (c instanceof ConstantInterfaceMethodref) {
        final ConstantInterfaceMethodref cim = (ConstantInterfaceMethodref) c;
        if (cim.getNameAndTypeIndex() == an_index) {
          if (res == null) {
            res = ConstantInterfaceMethodref.class;
          } else if (res == ConstantFieldref.class) {
            cim.setNameAndTypeIndex(max + 1);
            if (i < an_index) update(cim, true);
          }
        }
      }
    }
    return res;
  }

  /**
   *
   * @param a_class BCEL class representing java class attibute type
   * @return name of attibute of the given type
   */
  private String getStringFor(final Class a_class) {
    String result = "dummy";
    if (a_class == Code.class) result = "Code";
    else if (a_class == LineNumberTable.class) result = "LineNumberTable";
    else if (a_class == LocalVariableTable.class) result = "LocalVariableTable";
    else if (a_class == ExceptionTable.class) result = "Exceptions";
    else if (a_class == SourceFile.class) result = "SourceFile";
    else if (a_class == ConstantValue.class) result = "ConstantValue";
    return result;
  }

  /**
   *
   * @param a_class BCEL class representing java class attibute type
   * @return index for dummy constant for a given type
   */
  private int getDummyUtf(final Class a_class) {
    if (!my_dummy_utfs.containsKey(a_class)) return getDummyUtf();
    if (my_dummy_utfs.get(a_class) != -1) return my_dummy_utfs.get(a_class);
    my_constants.add(new ConstantUtf8(getStringFor(a_class)));
    my_dummy_utfs.put(a_class, my_constants.size() - 1);
    return my_dummy_utfs.get(a_class);
  }

  /**
   * Initializes indexes of dummy Utf8 constants for standard java
   * class attibutes to -1 (which means that those constants haven't been
   * added to the constant pool). <br> <br>
   *
   * TODO (Umbra) add Signature, PMGClass, etc.
   */
  private void initDummyUtfs() {
    my_dummy_utfs.put(Code.class, -1);
    my_dummy_utfs.put(LineNumberTable.class, -1);
    my_dummy_utfs.put(LocalVariableTable.class, -1);
    my_dummy_utfs.put(ExceptionTable.class, -1);
    my_dummy_utfs.put(SourceFile.class, -1);
    my_dummy_utfs.put(ConstantValue.class, -1);
  }

  /**
   *
   * @param an_attr an attribute
   * @return <code>true</code> if attribute an_attr has correct information
   * about its name in constant pool
   */
  private boolean properNameConstant(final Attribute an_attr) {
    boolean result = true;
    final Constant c =
      my_jc.getConstantPool().getConstant(an_attr.getNameIndex());
    if (!(c instanceof ConstantUtf8)) return false;
    final ConstantUtf8 cu8 = (ConstantUtf8) c;
    if (an_attr instanceof Code) result = cu8.getBytes().equals("Code");
    else if (an_attr instanceof LineNumberTable)
      result = cu8.getBytes().equals("LineNumberTable");
    else if (an_attr instanceof LocalVariableTable)
      result = cu8.getBytes().equals("LocalVariableTable");
    else if (an_attr instanceof ExceptionTable)
      result = cu8.getBytes().equals("Exceptions");
    else if (an_attr instanceof SourceFile)
      result = cu8.getBytes().equals("SourceFile");
    else if (an_attr instanceof ConstantValue)
      result = cu8.getBytes().equals("ConstantValue");
    return result;
  }

  /**
  *
  * @return Utf8 constant index with dummy exception class name
  */
  private int getDummyExceptionName() {
    if (my_dummy_exception_name_index != -1)
      return my_dummy_exception_name_index;
    my_constants.add(new ConstantUtf8("java/lang/Exception"));
    my_dummy_exception_name_index = my_constants.size() - 1;
    return my_dummy_exception_name_index;
  }

 /**
 *
 * @return dummy Class constant index representing dummy exception
 */
  private int getDummyException() {
    if (my_dummy_exception_index != -1) return my_dummy_exception_index;
    my_constants.add(new ConstantClass(getDummyExceptionName()));
    my_dummy_exception_index = my_constants.size() - 1;
    return my_dummy_exception_index;
  }

  /**
   *
   * @param a_const a constant
   * @return <code>true</code> if a_const is const Utf8 containing correct
   * type descriptor
   */
  public boolean isFieldDescriptor(final Constant a_const) {
    boolean result = false;
    if (!(a_const instanceof ConstantUtf8)) return false;
    final ConstantUtf8 cu8 = (ConstantUtf8) a_const;
    final String sig = cu8.getBytes();
    if (isNonArrayFieldDescriptor(sig)) result = true;
    else if (sig.startsWith("[")) {
      int i = 0;
      while (i < sig.length() && sig.charAt(i) == '[') i++;
      if (i < sig.length())
        result = isNonArrayFieldDescriptor(sig.substring(i));
    }
    return result;
  }

  /**
   *
   * @param a_sig type descriptor
   * @return <code>true</code> if a_sig is correct non-array descriptor
   */
  private boolean isNonArrayFieldDescriptor(final String a_sig) {
    boolean result = false;
    if (a_sig.equals("B")) result = true;
    else if (a_sig.equals("C")) result = true;
    else if (a_sig.equals("D")) result = true;
    else if (a_sig.equals("F")) result = true;
    else if (a_sig.equals("I")) result = true;
    else if (a_sig.equals("J")) result = true;
    else if (a_sig.equals("S")) result = true;
    else if (a_sig.equals("Z")) result = true;
    else if (a_sig.startsWith("L")) {
      boolean expect_part = false;
      boolean expect_slash = false;
      final boolean expect_start = true;
      result = true;
      if (a_sig.length() == 1) {
        result = false;
        return result;
      }
      final String sig = a_sig.substring(1);
      if (sig.charAt(sig.length() - 1) != ';') {
        result = false;
      } else {
        for (int i = 0; i < sig.length(); i++) {
          final char c = sig.charAt(i);
          if (!(expect_slash && c == '/') &&
              !(expect_start && Character.isJavaIdentifierStart(c)) &&
              !(expect_part && Character.isJavaIdentifierPart(c)) &&
              !(i == sig.length() - 1 && c == ';')) {
            result = false;
            break;
          }
          if (c != '/') {
            expect_part = true;
            expect_slash = true;
          } else {
            expect_part = false;
            expect_slash = false;
          }
        }
      }
    }
    return result;
  }

}
