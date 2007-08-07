/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.tests;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

import umbra.UmbraPlugin;

/**
 * TODO write description.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public final class BcelTestRun {

  /**
   * TODO.
   */
  static final String HW_CLASS_NAME = "umbra.test.HelloWorld";


  /**
   * TODO.
   */
  static final String HW_PATH_NAME = "bin\\umbra\\test\\HelloWorld.class";

  /**
   * TODO.
   */
  private static final int INSTRUCTION_TO_CHANGE_NO = 23;

  /**
   * TODO.
   */
  private static final int NO_OF_CHARS = 4096;

  /**
   * TODO.
   */
  private static final int NO_OF_LINES = 256;

  /**
   * This is a utility class so the constructor is declared to prevent
   * accidental creation of the instences of the class.
   */
  private BcelTestRun() {
  }

  /**
   * TODO.
   *
   * @param a_java_class TODO
   * @return TODO
   */
  public static JavaClass change_jc(final JavaClass a_java_class) {
    final ClassGen cg = new ClassGen(a_java_class);
    final ConstantPoolGen cpg = cg.getConstantPool();
    final Method[] methods = cg.getMethods();
    for (int i = 0; i < methods.length; i++) {
      workOnLDCInstructions(cpg, methods, i);
      cg.setConstantPool(cpg);
      cg.update();
      a_java_class.setConstantPool(a_java_class.getConstantPool());
      /* for (InstructionHandle pos = start; pos != end; pos = pos.getNext()) {
        Instruction ins = pos.getInstruction();
      }*/
    }
    return cg.getJavaClass();
  }

  /**
   * TODO.
   * @param a_cpg TODO
   * @param the_methods TODO
   * @param an_index TODO
   */
  private static void workOnLDCInstructions(final ConstantPoolGen a_cpg,
                                            final Method[] the_methods,
                                            final int an_index) {
    final MethodGen mg = new MethodGen(the_methods[an_index],
                                       HW_CLASS_NAME, a_cpg);
    final InstructionList il = mg.getInstructionList();
    final InstructionHandle start = il.getStart();
    final InstructionHandle end = il.getEnd();
    for (InstructionHandle pos = start; pos != end; pos = pos.getNext()) {
      final Instruction ins = pos.getInstruction();
      if ("ldc".equals(ins.getName())) { //we check here that arrays are OK too
        UmbraPlugin.messagelog(Integer.toString(a_cpg.getSize()));
        a_cpg.addString("CompDiff");
        final Constant con = a_cpg.getConstant(35);
        UmbraPlugin.messagelog("Index " +
                               ((ConstantString)con).getStringIndex());
        a_cpg.setConstant(INSTRUCTION_TO_CHANGE_NO, con);
        final Method mm = mg.getMethod();
        the_methods[an_index] = mm;
      }
    }
  }

  /**
   * TODO.
   * @param a_java_class TODO
   */
  public static void wypisz(final JavaClass a_java_class) {
    String bajtkod = "";
    final Method[] methods = a_java_class.getMethods();
    final byte[][] names = new byte[methods.length][NO_OF_LINES];
    final byte[][] code = new byte[methods.length][NO_OF_CHARS];
    final int[] namesLen = new int[methods.length];
    final int[] codeLen = new int[methods.length];
    for (int i = 0; i < methods.length; i++) {
      try {
        namesLen[i] = methods[i].toString().getBytes().length;
        names[i] = methods[i].toString().getBytes();
        codeLen[i] = methods[i].getCode().toString().length();
        code[i] = methods[i].getCode().toString().getBytes();
      } catch (NullPointerException e) {
        e.printStackTrace();
      }
    }
    final char[] contents = new char[NO_OF_CHARS];
    final int k = fillInContents(methods, names, code, namesLen,
                                 codeLen, contents);
    bajtkod = String.copyValueOf(contents, 0, k);
    UmbraPlugin.messagelog(bajtkod);

  }

  /**
   * TODO.
   * @param the_methods TODO
   * @param the_names TODO
   * @param the_code TODO
   * @param the_names_len TODO
   * @param the_code_len TODO
   * @param the_contents TODO
   * @return TODO
   */
  private static int fillInContents(final Method[] the_methods,
                                    final byte[][] the_names,
                                    final byte[][] the_code,
                                    final int[] the_names_len,
                                    final int[] the_code_len,
                                    final char[] the_contents) {
    int k = 0;
    for (int i = 0; i < the_methods.length; i++) {
      for (int j = 0; j < the_names_len[i]; j++, k++) {
        the_contents[k] = (char)the_names[i][j];
      }
      the_contents[k] = '\n';
      k++;
      for (int j = 0; j < the_code_len[i]; j++, k++) {
        the_contents[k] = (char)the_code[i][j];
      }
      the_contents[k] = '\n';
      k++;
    }
    the_contents[k] = '\0';
    return k;
  }
}
