package test;

import java.io.IOException;

import org.antlr.runtime.RecognitionException;

import annot.attributes.AType;
import annot.attributes.BCPrintableAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.IMessageLog;
import annot.bcclass.MLog;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.CodeSearch;
import annot.textio.IDisplayStyle;
import annot.textio.Parsing;

public class Testuj {

	private static boolean goShowTraceOnFailures = true;
	private static boolean goFullSaveAndLoadTests = true;
	private static boolean goShowFileChangesIfAny = false;

	private static int testC = 0;
	private static int errC = 0;

	private static BCClass bcc;
	private static int oldMask = 0;
	private static BCPrintableAttribute[] at;

	private static void test(boolean ok, int attr_id, String newval)
			throws IOException, ClassNotFoundException {
		test(ok, attr_id, newval, newval);
	}

	private static void test(boolean ok, int attr_id, String newval,
			String exprected) throws IOException, ClassNotFoundException {
		if (goFullSaveAndLoadTests)
			if (attr_id == 3)
				attr_id = 2;// ?
		testC++;
		try {
			BCPrintableAttribute pa = at[attr_id];
			String rc = IDisplayStyle.comment_next
					+ Parsing.purge(pa.last_code);
			String kw = CodeSearch.getKeyword(rc) + " ";
			newval = kw + newval;
			pa.parse(newval);
			at = bcc.getAllAttributes(AType.C_ALL);
			pa = at[attr_id];
			BMLConfig conf = new BMLConfig();
			String code = Parsing.purge(pa.printCode(conf));
			exprected = Parsing.purge(exprected);
			if (goFullSaveAndLoadTests) {
				if (!checkSaveAndLoad()) {
					at = bcc.getAllAttributes(AType.C_ALL);
					errC++;
					System.out.println(testC + ": cannot save \\ load");
					System.out.println("   " + newval);
					return;
				} else if (!checkSaveAndLoad()) {
					at = bcc.getAllAttributes(AType.C_ALL);
					errC++;
					System.out.println(testC + ": cannot 2 times save \\ load");
					System.out.println("   " + newval);
					return;
				} else {
					at = bcc.getAllAttributes(AType.C_ALL);
				}
			}
			if (!code.equals(kw + exprected)) {
				errC++;
				System.out.println(testC + ": misunderstood");
				System.out.println("   " + kw + exprected);
				System.out.println("   " + code);
				return;
			}
			if (ok) {
				System.out.println(testC + ": ok");
			} else {
				errC++;
				System.out.println(testC + ": correct");
				System.out.println("   " + newval);
			}
		} catch (RecognitionException e) {
			if (ok) {
				errC++;
				System.out.println(testC + ": failed");
				System.out.println("   " + newval);
				if (goShowTraceOnFailures)
					e.printStackTrace();
			} else {
				System.out.println(testC + ": ok");
			}
		}
	}

	private static void start() throws ClassNotFoundException,
			ReadAttributeException {
		bcc = OldTests.createSampleClass();
		at = bcc.getAllAttributes(AType.C_ALL);
		bcc.printCode();
		oldMask = MLog.mask;
		MLog.mask = IMessageLog.PERRORS;
		System.out.println(OldTests.xxx);
	}

	private static boolean checkSaveAndLoad() throws IOException,
			ClassNotFoundException {
		String code1 = bcc.printCode();
		bcc.saveToFile(Paths.tmp_path + "tmp3.class");
		try {
			bcc = new BCClass(Paths.tmp_path + "tmp3.class", "test.Empty2");
		} catch (ReadAttributeException e) {
			System.out.println("\nError while saving / loading");
			if (goShowFileChangesIfAny)
				System.out.println(bcc.printCode());
			if (goShowTraceOnFailures)
				e.printStackTrace();
			return false;
		}
		String code2 = bcc.printCode();
		if (!goFullSaveAndLoadTests)
			System.out.println();
		if (!code1.equals(code2)) {
			System.out
					.println("ERROR: bcclass changed while saving to / loading from file!");
			if (goShowFileChangesIfAny) {
				System.out.println("******** old file ********");
				System.out.println(code1);
				System.out.println("******** new file ********");
				System.out.println(code2);
			}
			return false;
		}
		return true;
	}

	private static void end() throws IOException, ClassNotFoundException {
		boolean ok = checkSaveAndLoad();
		MLog.mask = oldMask;
		if ((errC > 0) || (!ok)) {
			System.out.println("FAILURES!");
			if (errC == testC) {
				System.out.println("all tests failed!");
			} else {
				System.out.println(errC + " out of " + testC + " tests failed");
			}
		} else {
			System.out.println("OK.\nall " + testC + " tests passes.");
		}
	}

	private static void parserTest() throws ClassNotFoundException,
			ReadAttributeException, IOException {
		start();
		test(true, 0, "false");
		test(false, 0, "false true");
		test(true, 2, "true");
		test(true, 2, "false");
		test(true, 3, "false && true");
		test(true, 3, "false && true && false");
		test(true, 3, "false && true || false ==> true <==> false <=!=> true");
		test(true, 3, "(true && false) || (true && false)",
				"true && false || true && false");
		test(true, 3, "(true || false) && (true || false)");
		test(true, 2, "(((((true || false))) && true))",
				"(true || false) && true");
		test(true, 3, "1 < 2");
		test(false, 3, "(1)() < 2");

		test(true, 3, "true <=!=> false");
		test(true, 3, "true <=!=> false <==> true");
		test(true, 3, "((1 < (((2)))))", "1 < 2");
		test(true, 3, "1 < 2 <==> 3 < 4");
		test(true, 3, "1 < 2 <==> 3 < 4 <==> 5 < 6");
		test(true, 3, "1 < 2 ==> 3 < 4");
		test(true, 3, "true || false");
		test(true, 3, "true || 1 < 2 || true");
		test(false, 3, "true || 3");
		test(true, 3, "true && false");
		test(true, 3, "true && false || true");
		test(true, 3, "(true && false) || (false && true)",
				"true && false || false && true");
		test(true, 3, "(true || false) && (false || true)");
		test(true, 3, "1 > 2");
		test(true, 3, "1 < 2 && 3 <= 4 && 4 >= 5 && 6 > 7");
		test(false, 3, "1 > 2 > 3");
		test(false, 3, "true > false");
		test(true, 3, "1 == 2 && 3 != 4");
		test(false, 3, "1 == 2 == 3 && 4 != 5 != 6");
		test(false, 3, "1 == 2 != 3 && 4 != 5 == 6");
		test(false, 3, "1 == 2 == 3 < 4");
		test(false, 2, "1 > err");
		test(false, 2, "aaa && bbb < ccc");
		test(false, 2, "forall true");
		test(true, 2, "forall int a; a > 0");
		test(true, 2, "forall int a int b; a > b");
		test(false, 2, "forall int true; (true > 0)");
		test(true, 2, "forall int xyz; xyz > 0");
		test(true, 2, "(exists int a; a < 0) && (forall int b; b > 1)");
		test(true, 2, "forall int a; (exists int b; a < b)");
		test(true, 3, "(forall int a; a > 0) && 1 < 2");
		test(false, 3, "(forall int a; a > 0) && a < 1");
		test(true, 2, "forall int a; (exists int b; a < b) && a > 0");
		test(true, 2, "(forall int a; (exists int b; a < b)) && 1 > 0");
		test(false, 2, "(forall int a; (exists int b; a < b)) && a > 0");
		test(true, 3, "false || (forall int a; a > 0) && 1 < 2");
		test(true, 3, "forall boolean ok; ok");
		test(true, 3, "forall int i; (exists boolean b; i > 0 ==> b)");
		test(true, 3,
				"1 > 0 || (forall int i; (exists boolean b; i > 0 ==> b))");
		test(true, 3,
				"1 > 0 || (forall int i; (exists boolean b; i > 0 ==> b) ==> i < 0)");
		test(false, 3, "forall int i; i");
		test(false, 3, "forall int i; i ==> false");

		// test(true, 3, "(true ? 1 : 2) < 1");
		// test(true, 3, "(12 < 34 ? 1 : 2) < 45");
		// test(false, 3, "1 < 2 ? 3 : 4 < 5");
		// test(false, 3, "(1 < 2 ? 3 : 4 ? 5 : 6) < 7");
		// test(true, 3, "1 < 2 <==> (3 < 4 ? 7 : 8) < 9");
		// test(true, 3, "1 < 2 <==> (3 < 4 ? 5 : 6) < 7 <=!=> 8 < 9");
		// test(false, 3, "true <==> 3 ? 4 : 5 < 6");
		// test(true, 3, "(false ==> true ? 1 : 2) < 3");
		// test(false, 3, "false ==> true ==> false");

		// test(true, 3, "(1 | 2) > 0");
		// test(false, 3, "1 | 2 > 0");
		// test(false, 3, "1 & 2 > 3 ^ 4");
		// test(true, 3, "(1 ^ 2) > 0");
		// test(true, 3, "(1 & 2) > 0");
		// test(true, 3, "(1 | 2 | 3) > (4 ^ 5 & 6 ^ 7)");
		// test(true, 3, "(1 | 2 ^ 3 & (4 | 5)) > ((6 ^ 7) & 8)");
		// test(true, 3, "(1 | 2 ^ (3 & 4 | 5)) > (6 ^ 7 & 8)");

		// test(true, 3, "1 << 2 < 3");
		// test(true, 3, "1 >> 2 < 3 >>> 4");
		// test(true, 3, "1 << 2 << 3 + 4 >> 5 >> 6 + 7 >>> 8 >>> 9 < 10");
		// test(true, 3, "1 << 2 >> 3 >>> 4 << 5 < 6");

		// test(true, 3, "1 + 2 - 3 * 4 / 5 % 6 - 7 == 8");
		// test(true, 3, "(1 + 2) * (3 + 4) < 1 << 2 >> (3 + 4) * 5");
		// test(true, 3, "1 << (2 << 3) < 4", "1 << 2 << 3 < 4");
		// test(true, 3, "1 << 2 + (3 * 4) < 5", "1 << 2 + 3 * 4 < 5");
		// test(false, 3, "1 << 2 >> true < 3");
		// test(false, 3, "(1 << (2 >> true)) < 3"); //SEGV
		// test(false, 3, "1 << (2 >> true) < 3");

		// test(true, 3, "-1 < 2");
		// test(true, 3, "1 + -2 < 3");
		// test(false, 3, "--1 < 2 - -3");
		// test(true, 3, "-(-1) < 2 - -3", "--1 < 2 - -3");
		// test(true, 3, "-(+1) < +(-2) - +3", "-1 < -2 - 3");

		// test(true, 3, "NULL < 0");
		// test(true, 3, "NULL + 1 < 0");
		// test(false, 3, "NULL");
		// test(true, 3, "this < 0");
		// test(false, 3, "this.this < 0");
		// test(true, 3, "this.lv[1] < 1", "lo < 1");
		// test(true, 3, "this.lv[2].lv[1] < 2", "hi.lo < 2");
		end();
	}

	public static void main(String[] args) {
		try {
			parserTest();
			System.out.println("done.");
		} catch (Exception e) {
			System.out.println("error!");
			e.printStackTrace();
		}
	}

}
