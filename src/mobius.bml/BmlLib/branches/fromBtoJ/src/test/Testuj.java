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
import annot.bcclass.attributes.Assert;
import annot.bcclass.attributes.BCPrintableAttribute;
import annot.bcclass.attributes.SingleLoopSpecification;
import annot.bcio.AttributeReader;
import annot.bcio.ReadAttributeException;
import annot.formula.Predicate0Ar;

public class Testuj {

	static String path = Sciezka.path;
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
	public static void testuj(String clName) {
		try {
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
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}

	public static void ARunderstoodStats() {
		int br = AttributeReader.bytes_read;
		int bt = AttributeReader.bytes_total;
		System.out.println("Understood: " + br
				+ " bytes of " + bt + " ("
				+ (int)(100*br/bt) + "%)");
	}
	
	/**
	 * Displays all annotations from code displayed
	 *  from given class, with some information on them
	 *  (first generate and display code, then recognize
	 *  annotations in it).
	 * @param clName - class name
	 * @throws Exception - when something goes wrong.
	 */
	public static void parsingTest(String clName) {
		BCClass bcc;
		try {
			printHeader(clName);
			ClassPath cp = new ClassPath(path);
			JavaClass jc = SyntheticRepository.getInstance(cp).loadClass(clName);
			bcc = new BCClass(jc, true);
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
			return;
		} catch (ReadAttributeException e) {
			e.printStackTrace();
			return;
		}
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
				String code = bcc.parser.getCurrentCode(pra, str);
				System.out.println(code);
				System.out.println(bcc.parser.removeComment(code));
				parserTest(true, bcc.parser.removeComment(code));
				pra = a;
				o = i;
			}
		}
		showParserTestStats();
		count = errors = 0;
	}

	public static void ptInit() {
		ClassPath cp = new ClassPath(path);
		JavaClass jc;
		try {
			jc = SyntheticRepository.getInstance(cp).loadClass(clName5);
			bcc = new BCClass(jc, true);
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		} catch (ReadAttributeException e) {
			e.printStackTrace();
		}
	}
	
	private static int count = 0;
	private static int errors = 0;

	public static void parserTest(boolean ok, String str) {
//		str = str.replaceAll(" ", "");
		parserTest(ok, str, str);
	}

	public static void parserTest(boolean ok, String str, String result) {
		count++;
		System.out.println("---- test nr " + count + " ----");
		System.out.println("  parsing: "+bcc.parser.purge(str).substring(6) + (ok ? "" : " (err)"));
		try {
			BCMethod m = bcc.metody.elementAt(2);
			BCPrintableAttribute old = new Assert(Predicate0Ar.FALSE, 0, m);
			old.method = m;
			BMLConfig conf = new BMLConfig(bcc.getConstantPool());
			if (m != null)
				conf.currMethod = m.getBCELMethod();
			BCPrintableAttribute pa = bcc.parser.parseAttribute(old, str);
			if (!ok) {
				errors++;
				System.out.println("### this parsing should have failed!");
				return;
			}
			String out = pa.printCode(conf);
			String outp = bcc.parser.purge(out);
			result = bcc.parser.purge(result);
			if (result.equals(outp))
				return;
			errors++;
			System.out.println("  parsed : "+bcc.parser.removeComment(out));
			System.out.println("### attribute was not understood!");
		} catch (RecognitionException e) {
			if (!ok) {
				return;
			}
			errors++;
			System.out.println("### parsing error.");
		}
	}

	private static void showParserTestStats() {
		if (errors == 0) {
			System.out.println("\nSUCCESS\n all "
					+count+" tests passed.");
		} else {
			System.out.println("\nFAILURES!\n"
					+((errors < count) ? errors : "all")
					+" out of "+count+" tests failed.");
		}
	}
	
	private static void longParserTest() {
		parserTest(true, bcc.parser.removeComment("/*  assert # \n * \n */"));
		parserTest(true, "assert true");
		parserTest(true, "assert 1 < 2");
		parserTest(false, "assert (1)() < 2");
//		parserTest(true, "assert ((((((1)) < (((2)))))))", "assert 1 < 2"); //XXX: 2^n ??
		parserTest(true, "assert ((1 < (((2)))))", "assert 1 < 2");
		parserTest(true, "assert (true ? 1 : 2) < 1");
		parserTest(true, "assert (12 < 34 ? 1 : 2) < 45");
		parserTest(false, "assert 1 < 2 ? 3 : 4 < 5");
		parserTest(false, "assert (1 < 2 ? 3 : 4 ? 5 : 6) < 7");
		parserTest(true, "assert 1 < 2 <==> 3 < 4");
		parserTest(true, "assert 1 < 2 <==> 3 < 4 <==> 5 < 6");
		parserTest(true, "assert 1 < 2 <==> (3 < 4 ? 7 : 8) < 9");
		parserTest(true, "assert true <=!=> false");
		parserTest(true, "assert true <=!=> false <==> true");
		parserTest(true, "assert 1 < 2 <==> (3 < 4 ? 5 : 6) < 7 <=!=> 8 < 9");
		parserTest(false, "assert true <==> 3 ? 4 : 5 < 6");
		parserTest(true, "assert 1 < 2 ==> 3 < 4");
		parserTest(true, "assert (false ==> true ? 1 : 2) < 3");
		parserTest(false, "assert false ==> true ==> false");
		parserTest(true, "assert true || false");
		parserTest(true, "assert true || 1 < 2 || true");
		parserTest(false, "assert true || 3");
		parserTest(true, "assert true && false");
		parserTest(true, "assert true && false || true");
		parserTest(true, "assert (true && false) || (false && true)", "assert true && false || false && true");
		parserTest(true, "assert (true || false) && (false || true)");
		parserTest(true, "assert 1 > 2");
		parserTest(true, "assert 1 < 2 && 3 <= 4 && 4 >= 5 && 6 > 7");
		parserTest(false, "assert 1 > 2 > 3");
		parserTest(false, "assert true > false");
		parserTest(true, "assert (1 | 2) > 0");
		parserTest(false, "assert 1 | 2 > 0");
		parserTest(false, "assert 1 & 2 > 3 ^ 4");
		parserTest(true, "assert (1 ^ 2) > 0");
		parserTest(true, "assert (1 & 2) > 0");
		parserTest(true, "assert (1 | 2 | 3) > (4 ^ 5 & 6 ^ 7)");
		parserTest(true, "assert (1 | 2 ^ 3 & (4 | 5)) > ((6 ^ 7) & 8)");
		parserTest(true, "assert (1 | 2 ^ (3 & 4 | 5)) > (6 ^ 7 & 8)");
		parserTest(true, "assert 1 == 2 && 3 != 4");
		parserTest(false, "assert 1 == 2 == 3 && 4 != 5 != 6");
		parserTest(false, "assert 1 == 2 != 3 && 4 != 5 == 6");
		parserTest(false, "assert 1 == 2 == 3 < 4");
		parserTest(true, "assert 1 << 2 < 3");
		parserTest(true, "assert 1 >> 2 < 3 >>> 4");
		parserTest(true, "assert 1 << 2 << 3 + 4 >> 5 >> 6 + 7 >>> 8 >>> 9 < 10");
		parserTest(true, "assert 1 << 2 >> 3 >>> 4 << 5 < 6");
		parserTest(true, "assert 1 + 2 - 3 * 4 / 5 % 6 - 7 == 8");
		parserTest(true, "assert (1 + 2) * (3 + 4) < 1 << 2 >> (3 + 4) * 5");
		parserTest(true, "assert 1 << (2 << 3) < 4", "assert 1 << 2 << 3 < 4");
		parserTest(true, "assert 1 << 2 + (3 * 4) < 5", "assert 1 << 2 + 3 * 4 < 5");
		parserTest(false, "assert 1 << 2 >> true < 3");
//		parserTest(false, "assert (1 << (2 >> true)) < 3");  FIXME!! SEGV
		parserTest(false, "assert 1 << (2 >> true) < 3");
		parserTest(true, "assert -1 < 2");
		parserTest(true, "assert 1 + -2 < 3");
		parserTest(false, "assert --1 < 2 - -3");
		parserTest(true, "assert -(-1) < 2 - -3", "assert --1 < 2 - -3");
		parserTest(true, "assert -(+1) < +(-2) - +3", "assert -1 < -2 - 3");
		parserTest(true, "assert NULL < 0");
		parserTest(true, "assert NULL + 1 < 0");
		parserTest(false, "assert NULL");
		parserTest(true, "assert this < 0");
		parserTest(false, "assert this.this < 0");
		parserTest(true, "assert this.lv[1] < 1", "assert lo < 1");
		parserTest(true, "assert this.lv[2].lv[1] < 2", "assert hi.lo < 2");
		showParserTestStats();
	}
	
	public static void main(String[] args) {
		ptInit();
		longParserTest();
//		parsingTest(clName5);
	}
}
