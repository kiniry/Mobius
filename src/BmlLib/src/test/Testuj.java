package test;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

import annot.bcclass.BCClass;
import annot.bcio.AttributeReader;

public class Testuj {

	static String path = "D:\\dane\\workspace\\BmlLib\\src\\";
	static String clName1 = "test.List";
	static String clName2 = "test.TestNestedLoops";
	static String clName3 = "test.Loop";
	static String clName4 = "test.Toto";
	static String clName5 = "test.QuickSort";
	
	public static void printCP(JavaClass jc) {
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		System.out.println("Constant pool:");
		for (int i=1; i<cpg.getSize(); i++) {
			Constant c = cpg.getConstantPool().getConstant(i);
			if (c == null)
				System.out.println("  NULL("+i+")");
			else
				System.out.println("  "+i+": "+c.toString());
		}
	}
	
	public static void testuj(String clName) throws Exception {
		for (int i=0; i<80; i++)
			System.out.print("#");
		System.out.println("");
		int x = (80-(14+clName.length()))/2;
		for (int i=0; i<x; i++)
			System.out.print("#");
		System.out.print("   TESTING: "+clName+"   ");
		for (int i=0; i<x-(x%2); i++)
			System.out.print("#");
		System.out.println();
		for (int i=0; i<80; i++)
			System.out.print("#");
		System.out.println();
		ClassPath cp = new ClassPath(path);
		JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(clName);
		printCP(jc);
		System.out.println("*******************************************************************************************");
		BCClass bcc = new BCClass(jc);
		System.out.println("*******************************************************************************************");
		String str = bcc.printCode();
		System.out.println("*******************************************************************************************");
		System.out.print(str);
	}

	public static void main(String[] args) {
		try {
			testuj(clName1);
			testuj(clName2);
			testuj(clName3);
			testuj(clName4);
			testuj(clName5);
			int br = AttributeReader.bytes_read;
			int bt = AttributeReader.bytes_total;
			System.out.println("\nUnderstood: " + br
					+ " bytes of " + bt + " ("
					+ (int)(100*br/bt) + "%)");
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
