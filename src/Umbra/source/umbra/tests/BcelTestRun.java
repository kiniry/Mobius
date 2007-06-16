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

/**
 * TODO write description
 *
 * @author Wojtek & Tomek & Jarek
 */
public class BcelTestRun {

  static final String HWClName = "umbra.test.HelloWorld";
  static final String HWClNameW = "bin\\umbra\\test\\HelloWorld.class";

  public static JavaClass zmien_jc(final JavaClass jc)
  {
    final ClassGen cg = new ClassGen(jc);
    final ConstantPoolGen cpg = cg.getConstantPool();
    final Method[] methods = cg.getMethods();
    for (int i = 0; i < methods.length; i++) {
      final MethodGen mg = new MethodGen(methods[i], HWClName, cpg);
      final InstructionList il = mg.getInstructionList();
      final InstructionHandle start = il.getStart();
      final InstructionHandle end = il.getEnd();
      for (InstructionHandle pos = start; pos != end; pos = pos.getNext()) {
        final Instruction ins = pos.getInstruction();
        if ("ldc".equals(ins.getName())) {
            System.out.println(cpg.getSize());
            cpg.addString("CompDiff");
            final Constant con = cpg.getConstant(35);
            System.out.println("Index " + ((ConstantString)con).getStringIndex());
            cpg.setConstant(23, con);
            final Method mm = mg.getMethod();
            methods[i] = mm;
        }
      }
      cg.setConstantPool(cpg);
      cg.update();
      jc.setConstantPool(jc.getConstantPool());
      /* for (InstructionHandle pos = start; pos != end; pos = pos.getNext()) {
        Instruction ins = pos.getInstruction();
      }*/
    }
    return cg.getJavaClass();
  }

  public static void wypisz(final JavaClass jc)
  {
    String bajtkod = "";
    final Method[] methods = jc.getMethods();
    final byte[][] names = new byte[methods.length][256];
    final byte[][] code = new byte[methods.length][4096];
    final int[] namesLen = new int[methods.length];
    final int[] codeLen = new int[methods.length];
    for(int i = 0; i < methods.length; i++) {
      try {
        namesLen[i] = methods[i].toString().getBytes().length;
        names[i] = methods[i].toString().getBytes();
        codeLen[i] = methods[i].getCode().toString().length();
        code[i] = methods[i].getCode().toString().getBytes();
      } catch (NullPointerException e) {
        e.printStackTrace();
      }
    }
    final char[] contents = new char[4096];
    int k = 0;
    for(int i = 0; i < methods.length; i++) {
      for(int j = 0; j < namesLen[i]; j++, k++) {
        contents[k] = (char)names[i][j];
      }
      contents[k] = '\n';
      k++;
      for(int j = 0; j < codeLen[i]; j++, k++) {
        contents[k] = (char)code[i][j];
      }
      contents[k] = '\n';
      k++;
    }
    contents[k] = '\0';
    bajtkod = String.copyValueOf(contents, 0, k);
    System.out.println(bajtkod);

  }
}
