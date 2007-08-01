package test;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.BMLConfig;
import annot.bcclass.attributes.BCPrintableAttribute;
import annot.bcio.AttributeReader;
import annot.bcio.ReadAttributeException;

public class Testuj {

	static String path = "D:\\dane\\workspace\\BmlLib\\src\\";
	static String clName1 = "test.List";
	static String clName2 = "test.TestNestedLoops";
	static String clName3 = "test.Loop";
	static String clName4 = "test.Toto";
	static String clName5 = "test.QuickSort";

	private static BCClass bcc;
	
	/**
	 * prints constantpool of given JavaClass.
	 * 
	 * @param jc - JavaClass
	 */
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
	
	/**
	 * prints given class name, surrounded by hashes.
	 * @param clName - class name.
	 */
	public static void printHeader(String clName) {
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
	}
	
	public static void printStars() {
		System.out.println("*******************************************************************************************");
	}

	/**
	 * Add line number to the beginning of each line
	 * of given String. 
	 * 
	 * @param str - string to be procesed
	 * @return <code>str</code> with "line i: " at the
	 * 				beginning of i-th line.
	 */
	public static String addLineNumbers(String str) {
		String ret = "";
		String[] lines = str.split("\n");
		for (int i=0; i<lines.length; i++)
			ret += "line " + i + ":  " + lines[i] + "\n";
		return ret;
	}
	
	/**
	 * Loads and displays bytecode with annotations
	 * 	of given class.
	 * @param clName - class name (see path constant).
	 * @throws Exception - if something goes wrong.
	 */
	public static void testuj(String clName) throws Exception {
		printHeader(clName);
		ClassPath cp = new ClassPath(path);
		JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(clName);
		printCP(jc);
		printStars();
		BCClass bcc = new BCClass(jc);
		printStars();
		String str = bcc.printCode();
		printStars();
		System.out.print(str);
	}

	/**
	 * Displays all annotations from code displayed
	 *  from given class, with some information on them
	 *  (first generate and display code, then recognize
	 *  annotations in it).
	 * @param clName - class name
	 * @throws Exception - when something goes wrong.
	 */
	public static void parsingTest(String clName) throws Exception {
		printHeader(clName);
		ClassPath cp = new ClassPath(path);
		JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(clName);
		BCClass bcc = new BCClass(jc);
		String str = bcc.printCode();
		String[] lines = str.split("\n");
		printStars();
		System.out.println(addLineNumbers(str));
		printStars();
		System.out.println("length = " + lines.length);
		BCPrintableAttribute pra = null;
		int o = -1;
		for (int i=0; i<lines.length; i++) {
			BCPrintableAttribute a = bcc.parser.getAttributeAtLine(str, i);
			if (pra == null) {
				pra = a;
				o = i;
				continue;
			} else {
				if (a == pra)
					continue;
				System.out.println("line: " + o + " -- " + (i-1)
						+ ", attribute: " + pra.atype);
				if (pra.pcIndex >= 0)
					System.out.println("   method: "
							+ pra.method.getHeader()
							+ ", pc: " + pra.pcIndex
							+ ", lines: " + pra.line_start
							+ " -- " + pra.line_end);
				System.out.println(
						bcc.parser.getCurrentCode(pra, str));
				pra = a;
				o = i;
			}
		}
	}

	public static void ptInit() {
		ClassPath cp = new ClassPath(path);
		JavaClass jc;
		try {
			jc = SyntheticRepository.getInstance(cp).loadClass(clName5);
			bcc = new BCClass(jc);
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
		printStars();
	}
	
	public static void parserTest(String str) {
		System.out.println("parsing:\n"+str);
		try {
			BCMethod m = null;
			BCPrintableAttribute old = new BCPrintableAttribute();
			old.method = m;
			BMLConfig conf = new BMLConfig(bcc.getConstantPool());
			if (m != null)
				conf.currMethod = m.getBCELMethod();
			BCPrintableAttribute pa = bcc.parser.parseAttribute(old, str);
			String out = pa.printCode(conf);
			System.out.println("understood:\n"+out);
		} catch (RecognitionException e) {
			System.out.flush();
			System.err.flush();
			System.err.println("parsing error.");
		}
	}
	
	public static void main(String[] args) {
		try {
			ptInit();
//			testuj(clName1);
//			testuj(clName2);
//			testuj(clName3);
//			testuj(clName4);
//			testuj(clName5);
//			parsingTest(clName5);
			parserTest(bcc.parser.removeComment("/* assert ? \n * \n */"));
//			int br = AttributeReader.bytes_read;
//			int bt = AttributeReader.bytes_total;
//			System.out.println("Understood: " + br
//					+ " bytes of " + bt + " ("
//					+ (int)(100*br/bt) + "%)");
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
