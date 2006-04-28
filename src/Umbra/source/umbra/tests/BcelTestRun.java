package umbra.tests;

import java.io.IOException;

import org.apache.bcel.Repository;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.TargetLostException;
import org.eclipse.jface.text.Document;

/**
 * @author Wojtek & Tomek & Jarek
 */
public class BcelTestRun {

	final static String HWClName = "umbra.test.HelloWorld";
	final static String HWClNameW = "bin\\umbra\\test\\HelloWorld.class";

	public static JavaClass zmien_jc(JavaClass jc)
	{
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		Method[] methods = cg.getMethods();
		for (int i = 0; i < methods.length; i++) {
			MethodGen mg = new MethodGen(methods[i], HWClName, cpg);
			InstructionList il = mg.getInstructionList();
			InstructionHandle start = il.getStart();
			InstructionHandle end = il.getEnd();
			for (InstructionHandle pos = start; pos != end; pos = pos.getNext()) {
				Instruction ins = pos.getInstruction();
				if (ins.getName() == "ldc") {
						Constant[] cpk1 = jc.getConstantPool().getConstantPool();
						System.out.println(cpg.getSize());
						cpg.addString("CompDiff");
						Constant con = cpg.getConstant(35);
						System.out.println("Index " + ((ConstantString)con).getStringIndex());
						cpg.setConstant(23, con);
						Method mm = mg.getMethod();
						methods[i] = mm;
				}
			}
			cg.setConstantPool(cpg);
			cg.update();
			jc.setConstantPool(jc.getConstantPool());
			for (InstructionHandle pos = start; pos != end; pos = pos.getNext()) {
				Instruction ins = pos.getInstruction();
			}
		}
		return cg.getJavaClass();
	}
	
	public static void wypisz(JavaClass jc)
	{
		String bajtkod = "";
		Method[] methods = jc.getMethods();
		byte[][] names = new byte[methods.length][256];
		byte[][] code = new byte[methods.length][4096];
		int[] namesLen = new int[methods.length];
		int[] codeLen = new int[methods.length];
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
		char[] contents = new char[4096];
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
	
	public static void main(String[] args)
	{
		JavaClass jc = Repository.lookupClass(HWClName);
		System.out.println("----- przed zmian¹ -----");
		wypisz(jc);
		jc = zmien_jc(jc);
		System.out.println("-----  po zmianie  -----");
		wypisz(jc);
		try {
			jc.dump(HWClNameW);
			System.out.println("zapisany ");
		} catch (IOException e) {
			System.out.println("jest kiepsko!");
			e.printStackTrace();
		}
	}
}
