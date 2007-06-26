package umbra.tests;

import java.io.IOException;

import org.apache.bcel.Repository;
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
 * TODO write description
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BcelTestRun {

  /**
   * TODO
   */
  private static final int INSTRUCTION_TO_CHANGE_NO = 23;

  /**
   * TODO
   */
  private static final int NO_OF_CHARS = 4096;

  /**
   * TODO
   */
  private static final int NO_OF_LINES = 256;

  /**
   * TODO
   */
  static final String HWClName = "umbra.test.HelloWorld";

  /**
   * TODO
   */
  static final String HWClNameW = "bin\\umbra\\test\\HelloWorld.class";

  /**
   * TODO
   *
   * @param a_java_class
   * @return
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
   * TODO
   * @param cpg
   * @param methods
   * @param i
   */
  private static void workOnLDCInstructions(final ConstantPoolGen cpg,
                                            final Method[] methods,
                                            final int i) {
    final MethodGen mg = new MethodGen(methods[i], HWClName, cpg);
    final InstructionList il = mg.getInstructionList();
    final InstructionHandle start = il.getStart();
    final InstructionHandle end = il.getEnd();
    for (InstructionHandle pos = start; pos != end; pos = pos.getNext()) {
      final Instruction ins = pos.getInstruction();
      if ("ldc".equals(ins.getName())) {
        UmbraPlugin.messagelog(Integer.toString(cpg.getSize()));
        cpg.addString("CompDiff");
        final Constant con = cpg.getConstant(35);
        UmbraPlugin.messagelog("Index " + ((ConstantString)con).getStringIndex());
        cpg.setConstant(INSTRUCTION_TO_CHANGE_NO, con);
        final Method mm = mg.getMethod();
        methods[i] = mm;
      }
    }
  }

  /**
   * TODO
   * @param a_java_class
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
   * TODO
   * @param methods
   * @param names
   * @param code
   * @param namesLen
   * @param codeLen
   * @param contents
   * @return
   */
  private static int fillInContents(final Method[] methods,
                                    final byte[][] names,
                                    final byte[][] code,
                                    final int[] namesLen,
                                    final int[] codeLen,
                                    final char[] contents) {
    int k = 0;
    for (int i = 0; i < methods.length; i++) {
      for (int j = 0; j < namesLen[i]; j++, k++) {
        contents[k] = (char)names[i][j];
      }
      contents[k] = '\n';
      k++;
      for (int j = 0; j < codeLen[i]; j++, k++) {
        contents[k] = (char)code[i][j];
      }
      contents[k] = '\n';
      k++;
    }
    contents[k] = '\0';
    return k;
  }
}
