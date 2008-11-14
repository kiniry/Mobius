/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantDouble;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantFloat;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantInterfaceMethodref;
import org.apache.bcel.classfile.ConstantLong;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;

import annot.textio.DisplayStyle;

/**
 * The class handles the printing actions for elements of a constant pool.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public abstract class BCCConstantPrinting {

  /**
   * The array which contains the types of constants which are primitive
   * i.e. do not refer to other constant pool entries.
   */
  private static final byte[] PRIMITIVE_TYPES = {Constants.CONSTANT_Utf8,
                                                 Constants.CONSTANT_Integer,
                                                 Constants.CONSTANT_Float,
                                                 Constants.CONSTANT_Long,
                                                 Constants.CONSTANT_Double };

  /**
   * Gives a constant from constant pool. Constants from
   * second constant pool have indexes starting with
   * <code>initialSize</code>, while constants from primary
   * constant pool have indexes from 0 to initialSize - 1.
   * Can be used in loading from file only.
   *
   * @param i - constant index
   * @return i-th constant.
   */
  public abstract Constant getConstant(final int i);

  /**
   * Displays i-th constant. The format is as follows:
   *   constant-pool-line ::= const cp-ref = constant-pool-entry
   *                                                  [ constant-pool-comment ]
   * where
   *   cp-ref ::= #decimal-numeral
   *   constant-pool-entry ::= class-cp-entry | field-cp-entry
   *                       | method-cp-entry | interface-method-cp-entry
   *                       | string-cp-entry | integer-cp-entry
   *                       | float-cp-entry  | long-cp-entry | double-cp-entry
   *                       | name-and-type-cp-entry | utf8-cp-entry
   *
   * @param i - constant's index.
   * @return a String like described above.
   */
  protected String printElement(final int i) {
    final Constant c = getConstant(i);
    if (c == null) {
      return "";
    }
    return "  " + DisplayStyle.CONST_KWD + " " + printCPRef(i) + " " +
           DisplayStyle.EQUALS_SIGN + " " + printConstantPoolEntryData(c) +
           " // " + c.toString() +
           "\n";
  }

  /**
   * Prints out a single constant pool entry. It checks the type of the entry
   * and depending on that prints out a particular kind of constant pool entry.
   * The grammar is as follows:
   *   constant-pool-entry ::= class-cp-entry | field-cp-entry
   *                       | method-cp-entry | interface-method-cp-entry
   *                       | string-cp-entry | integer-cp-entry
   *                       | float-cp-entry  | long-cp-entry | double-cp-entry
   *                       | name-and-type-cp-entry | utf8-cp-entry
   * where
   *   class-cp-entry ::= Class cp-ref;
   *   field-cp-entry ::= Fieldref cp-ref.cp-ref;
   *   method-cp-entry ::= Methodref cp-ref.cp-ref;
   *   interface-method-cp-entry ::= InterfaceMethodref cp-ref.cp-ref;
   *   string-cp-entry ::= String cp-ref;
   *   integer-cp-entry ::= Integer [ sign ] decimal-integer-literal;
   *   float-cp-entry ::= Float [ sign ] floating-point-literal;
   *   long-cp-entry ::= Long [ sign ] decimal-integer-literal;
   *   float-cp-entry ::= Double [ sign ] floating-point-literal;
   *   name-and-type-cp-entry ::= NameAndType cp-ref.cp-ref;
   *   utf8-cp-entry ::= Utf8 [ string-character ]...;
   *   cp-ref ::= #decimal-numeral
   *
   * @param cnst a constant to be printed out
   * @return a string which contains the printed entry
   */
  private String printConstantPoolEntryData(final Constant cnst) {
    //handle primitive types
    if (isPrimitiveType(cnst.getTag())) {
      return printPrimitiveTypeConstant(cnst) + DisplayStyle.SEMICOLON_SIGN;
    }
    //handle references to constant pool
    String res = "";
    switch (cnst.getTag()) {
      case Constants.CONSTANT_Class:
        res = printClassConst(cnst);
        break;
      case Constants.CONSTANT_Fieldref:
        res = printFieldrefConst(cnst);
        break;
      case Constants.CONSTANT_String:
        res = printStringConst(cnst); break;
      case Constants.CONSTANT_Methodref:
        res = printMethodrefConst(cnst); break;
      case Constants.CONSTANT_InterfaceMethodref:
        res = printInterfaceMethodrefConst(cnst); break;
      case Constants.CONSTANT_NameAndType:
        res = printNameAndTypeConst(cnst); break;
      default:
        res = cnst.toString();
    }
    return res + DisplayStyle.SEMICOLON_SIGN;
  }

  /**
   * Checks if the given tag corresponds to a primitive type in the constant
   * pool. A type is primitive when it is not a reference to other item in
   * the constant pool.
   *
   * @param tag the value of the type to check
   * @return <code>true</code> in case the type belongs to primitive types.
   */
  private boolean isPrimitiveType(final byte tag) {
    for (int i = 0; i < PRIMITIVE_TYPES.length; i++) {
      if (tag == PRIMITIVE_TYPES[i]) return true;
    }
    return false;
  }

  /**
   * The method prints out the line corresponding to a constant of a primitive
   * type. In case the constant is not of a primitive type then it prints out
   * "UNKNOWN KEYWORD" and "UNKNOWN DATA".
   *
   * @param cnst the constant to print out
   * @return the string which contains the printed out constant
   */
  private String printPrimitiveTypeConstant(final Constant cnst) {
    String kwd = "";
    String bts = "";
    switch (cnst.getTag()) {
      case Constants.CONSTANT_Utf8:
        kwd = DisplayStyle.UTF8_KWD;
        bts = "\"" +
          ((ConstantUtf8)cnst).getBytes().replace("\n", "\\n") +
          "\"";
        break;
      case Constants.CONSTANT_Integer:
        kwd = DisplayStyle.INTEGER_KWD;
        bts = Integer.toString(((ConstantInteger)cnst).getBytes());
        break;
      case Constants.CONSTANT_Float:
        kwd = DisplayStyle.FLOAT_KWD;
        bts = Float.toString(((ConstantFloat)cnst).getBytes());
        break;
      case Constants.CONSTANT_Long:
        kwd = DisplayStyle.LONG_KWD;
        bts = Long.toString(((ConstantLong)cnst).getBytes()) + "L";
        break;
      case Constants.CONSTANT_Double:
        kwd = DisplayStyle.DOUBLE_KWD;
        bts = Double.toString(((ConstantDouble)cnst).getBytes()) + "D";
        break;
      default:
        kwd = "UNKNOWN KEYWORD";
        bts = "UNKNOWN DATA";
    }
    return kwd + " " + bts;
  }

  /**
   * The method prints out the line corresponding to a constant of the String
   * type. No check is done to verify the type. In case the type is wrong
   * {@link ClassCastException} is thrown.
   *
   * @param cnst the constant to print out
   * @return the string which contains the printed out constant
   */
  private String printStringConst(final Constant cnst) {
    String res;
    res = DisplayStyle.STRING_KWD + " " +
      printCPRef(((ConstantString)cnst).getStringIndex());
    return res;
  }

  /**
   * The method prints out the line corresponding to a constant of the Class
   * type. No check is done to verify the type. In case the type is wrong
   * {@link ClassCastException} is thrown.
   *
   * @param cnst the constant to print out
   * @return the string which contains the printed out constant
   */
  private String printClassConst(final Constant cnst) {
    String res;
    res = DisplayStyle.CLASS_KWD + " " +
      printCPRef(((ConstantClass)cnst).getNameIndex());
    return res;
  }

  /**
   * The method prints out the line corresponding to a constant of the
   * NameAndType type. No check is done to verify the type. In case the type is
   * wrong {@link ClassCastException} is thrown.
   *
   * @param cnst the constant to print out
   * @return the string which contains the printed out constant
   */
  private String printNameAndTypeConst(final Constant cnst) {
    String res;
    res = DisplayStyle.NAMEANDTYPE_KWD + " " +
      printCPRef(((ConstantNameAndType)cnst).getNameIndex()) +
      DisplayStyle.COLON_SIGN +
      printCPRef(((ConstantNameAndType)cnst).getSignatureIndex());
    return res;
  }

  /**
   * The method prints out the line corresponding to a constant of the
   * InterfaceMethodref type. No check is done to verify the type. In case the
   * type is wrong {@link ClassCastException} is thrown.
   *
   * @param cnst the constant to print out
   * @return the string which contains the printed out constant
   */
  private String printInterfaceMethodrefConst(final Constant cnst) {
    String res;
    res = DisplayStyle.INTERFACEMETHODREF_KWD + " " +
      printCPRef(((ConstantInterfaceMethodref)cnst).getClassIndex()) +
      DisplayStyle.DOT_SIGN +
      printCPRef(((ConstantInterfaceMethodref)cnst).getNameAndTypeIndex());
    return res;
  }

  /**
   * The method prints out the line corresponding to a constant of the
   * Methodref type. No check is done to verify the type. In case the type is
   * wrong {@link ClassCastException} is thrown.
   *
   * @param cnst the constant to print out
   * @return the string which contains the printed out constant
   */
  private String printMethodrefConst(final Constant cnst) {
    String res;
    res = DisplayStyle.METHODREF_KWD + " " +
      printCPRef(((ConstantMethodref)cnst).getClassIndex()) +
      DisplayStyle.DOT_SIGN +
      printCPRef(((ConstantMethodref)cnst).getNameAndTypeIndex());
    return res;
  }

  /**
   * The method prints out the line corresponding to a constant of the
   * Fieldref type. No check is done to verify the type. In case the type is
   * wrong {@link ClassCastException} is thrown.
   *
   * @param cnst the constant to print out
   * @return the string which contains the printed out constant
   */
  private String printFieldrefConst(final Constant cnst) {
    String res;
    res = DisplayStyle.FIELDREF_KWD + " " +
      printCPRef(((ConstantFieldref)cnst).getClassIndex()) +
      DisplayStyle.DOT_SIGN +
      printCPRef(((ConstantFieldref)cnst).getNameAndTypeIndex());
    return res;
  }

  /**
   * The method prints out a reference to the given constant pool entry. The
   * format is such that the hash ({@link DisplayStyle#HASH_SIGN}) is
   * printed out followed by the number the reference refers to.
   *
   * @param ref the reference to a constant pool entry
   * @return the string which contains the printed out reference
   */
  private String printCPRef(final int ref) {
    return DisplayStyle.HASH_SIGN + ref;
  }

}
