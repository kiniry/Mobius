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

/**
 * Automated test cases with deterministic scenario.
 * 
 * @author tomekb
 */
public final class Testuj {

	/**
	 * wether show stac trace of exception in test failures
	 * or not.
	 */
	private static boolean goShowTraceOnFailures = true;

	/**
	 * Perform "save and load" test after each example.
	 * This slows tests down a little, but also checks test
	 * annotations if they are saved and loaded correctly.
	 */
	private static boolean goFullSaveAndLoadTests = true;

	/**
	 * Show old and new class' bytecode if it has changed
	 * during saving / loading.
	 */
	private static boolean goShowFileChangesIfAny = false;

	/**
	 * Number of tests ran so far.
	 */
	private static int testC = 0;

	/**
	 * Number of errors occured so far.
	 */
	private static int errC = 0;

	/**
	 * Sample bytecode class ("Empty2.class").
	 */
	private static BCClass bcc;

	/**
	 * MLog original display mask.
	 * Number of syso messages will be reduced during tests,
	 * then restored to it's previous value.
	 */
	private static int oldMask = 0;

	/**
	 * Array of all annotations from test class.
	 */
	private static BCPrintableAttribute[] at;

	// Methods below can throw many exception that are catched
	// in main method. These exceptions usually means an error
	// in BmlLib library (unless Paths are set incorrectly)
	// and won't be described in JavaDocs.

	/**
	 * @see #test(boolean, int, String, String)
	 */
	private static void test(boolean ok, int attr_id, String newval)
			throws IOException, ClassNotFoundException {
		test(ok, attr_id, newval, newval);
	}

	/**
	 * Runs single test. Tries to parse an attribute, and
	 * perform "save and load" test,
	 * if {@link #goFullSaveAndLoadTests} flag is on.
	 * Updates test statistics and displays current tests
	 * result.
	 * 
	 * @param ok - wether this test should fail or not
	 * 		(wether <code>newval</code> is correct or not),
	 * @param attr_id - index of attribute to be altered,
	 * @param newval - new String representation of
	 * 		<code>at[attr_id]</code> attribute, to be parsed,
	 * @param exprected - expected String representation of
	 * 		new annotation (result of printCode(conf), called
	 * 		after parsing that annotation). It can slightly
	 * 		differ from <code>newval</code>, becouse eg. stray
	 * 		parenthness are removed this way.
	 */
	private static void test(boolean ok, int attr_id, String newval,
			String exprected) throws IOException, ClassNotFoundException {
		if (goFullSaveAndLoadTests)
			if (attr_id == 3)
				attr_id = 2;// ?
		testC++;
		try {
			BCPrintableAttribute pa = at[attr_id];
			String rc = IDisplayStyle.comment_next
					+ Parsing.purge(pa.getLast_code());
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

	/**
	 * Initializes parser tests.
	 */
	private static void start() throws ClassNotFoundException,
			ReadAttributeException {
		bcc = OldTests.createSampleClass();
		at = bcc.getAllAttributes(AType.C_ALL);
		bcc.printCode();
		oldMask = MLog.mask;
		MLog.mask = IMessageLog.PERRORS;
		System.out.println(OldTests.xxx);
	}

	/**
	 * A "save and load" test (Displays BCClass, saves it to
	 * a file and then loads from it, displays again and
	 * compares to previously displayd String. Both Strings
	 * should be equal).
	 * 
	 * @return wether test was successful or not.
	 */
	private static boolean checkSaveAndLoad() throws IOException,
			ClassNotFoundException {
		String code1 = bcc.printCode();
		bcc.saveToFile(Paths.tmp_path + "test\\tmp03.class");
		try {
			bcc = new BCClass(Paths.tmp_path, "test.tmp03");
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

	/**
	 * Finalizes tests and displays tests sumary.
	 */
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

	/**
	 * This method contains all test cases. New cases should
	 * be added here.
	 */
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
		test(true, 3, "1 > 0 || (forall int i; (exists boolean b; i > 0 ==> b))");
		test(true, 3, "1 > 0 || (forall int i; (exists boolean b; i > 0 ==> b) ==> i < 0)");
		test(false, 3, "forall int i; i");
		test(false, 3, "forall int i; i ==> false");
		test(false, 3, "forall int a itn b; a < b");
		test(false, 3, "forall int a int a; a < 0");
		test(false, 3, "forall int a int b; (exists int b; true)");
		test(true, 3, "forall int a int c; (exists int b; true)");
		test(true, 2, "forall int a boolean b; (exists int c; a < c && b) && (exists int c; a >= c)");
		test(true, 3, "forall int a; (exists int b; (forall int c; a <= b ==> b >= c))");

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

	/**
	 * Main method for running these tests.
	 * 
	 * @param args - unused.
	 */
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
