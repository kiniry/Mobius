package test;

import java.io.IOException;
import java.util.Random;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.attributes.AType;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.ClassInvariant;
import annot.attributes.InCodeAttribute;
import annot.attributes.MethodSpecification;
import annot.attributes.SingleAssert;
import annot.attributes.SpecificationCase;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcexpression.BoundVar;
import annot.bcexpression.JavaType;
import annot.bcexpression.NumberLiteral;
import annot.formula.AbstractFormula;
import annot.formula.Formula;
import annot.formula.Predicate0Ar;
import annot.formula.Predicate2Ar;
import annot.formula.QuantifiedFormula;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.BMLParser;
import annot.textio.CodeFragment;
import annot.textio.CodeSearch;
import annot.textio.Parsing;

/**
 * Manual tests for BmlLib library. After running some
 * of this scenarios, tester should take a look to the console
 * and check if all displayed values are as expected.
 * Some parts of this tests are undeterministic, so it'n not
 * possible to memorize all results and check if one displayed
 * is equal to the correct one, stored eg. in a file.
 * 
 * @author tomekb
 */
public final class OldTests {

	/**
	 * Wether random formula generator should also generate
	 * ugly, unproportial quantified formula to make it's
	 * formatting more difficult, or not.
	 */
	public static final boolean goGenerateRandomQuantifiedFormulas = true;

	/**
	 * If a flag above is on, this flag controls wether
	 * random formula generator should generate only
	 * 3args quantified formulas (with exactly one
	 * implication at the root) or not.
	 */
	public static final boolean go3argQuantifiersGenerated = true;

	/**
	 * Simple line hashes, for separating data printed to
	 * the console.
	 */
	public static final String xxx = "################################################################################";

	/**
	 * A class used for tests.
	 */
	private static BCClass bcc;

	/**
	 * Current test's number.
	 */
	private static int test_nr = 0;
	
	/**
	 * Test class's (bcc's) code.
	 */
	private static String code;
	
	/**
	 * A random stream.
	 */
	private static Random random;

	/**
	 * @return random non-negative integer value.
	 */
	private static int rand() {
		try {
			if (random == null)
				random = Random.class.newInstance();
			int ret = (random.nextInt());
			return (ret > 0) ? ret : -ret;
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println("Random generator fails!");
			throw new RuntimeException("environment error!");
		}
	}

	/**
	 * Generates a random formula, of size less or equal than
	 * given value.
	 * 
	 * @param size - maximum size of generaed formula.
	 * @return random formula with basic predicates,
	 * 		formulas and quantifiers (but without bound
	 * 		variables except it's declarations at quantifiers).
	 */
	private static AbstractFormula generateRandomFormula(int size) {
		return grf(size, 0.5, 0);
	}

	/**
	 * Generates a random formula.
	 * 
	 * @param size - maximum formula depth,
	 * @param w - width (?) of generated formula,
	 * @param ind - index of next bound variable names.
	 * @return random formula.
	 */
	private static AbstractFormula grf(int size, double w, int ind) {
		int[] connectors = { Code.TRUE, Code.FALSE, Code.NOT, Code.AND,
				Code.OR, Code.IMPLIES, Code.FORALL_WITH_NAME,
				Code.EXISTS_WITH_NAME };
		String[] names = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j" };
		int n = connectors.length;
		if (!goGenerateRandomQuantifiedFormulas)
			n -= 2;
		int r = rand() % n;
		if (w > 1)
			w = 1;
		r = (int) (r * w + (n - 1) * (1.0 - w));
		if (size <= 0)
			r = r % 2;
		int code = connectors[r];
		int s = size - 1;
		switch (code) {
		case Code.AND:
		case Code.OR:
		case Code.IMPLIES:
			return new Formula(code, grf(s, w + 0.1, ind), grf(s, w + 0.1, ind));
		case Code.NOT:
			return new Formula(code, grf(s, w + 0.1, ind));
		case Code.TRUE:
			return Predicate0Ar.TRUE;
		case Code.FALSE:
			return Predicate0Ar.FALSE;
		case Code.FORALL_WITH_NAME:
		case Code.EXISTS_WITH_NAME:
			QuantifiedFormula qf = new QuantifiedFormula(code);
			int bvc = rand() % 3 + 1;
			for (int i = 0; i < bvc; i++) {
				qf.addVariable(new BoundVar(JavaType.JavaInt, ind, qf,
						names[ind % names.length]));
				ind++;
			}
			AbstractFormula f;
			if (go3argQuantifiersGenerated) {
				AbstractFormula f1 = grf(s, w + 0.1, ind);
				AbstractFormula f2 = grf(s, w + 0.1, ind);
				f = new Formula(Code.IMPLIES, f1, f2);
			} else {
				f = grf(s, w + 0.1, ind);
			}
			qf.setFormula(f);
			return qf;
		default:
			throw new RuntimeException("error in generateRandomFormula");
		}
	}

	/**
	 * Creates a pseudo-random formula. Each call of this
	 * function with the same parameters will give the same
	 * formula (similar, but not the same object).
	 * 
	 * @param size - depth of generated formula,
	 * @param seed - another parameter,
	 * @return a formula, containing (at most) true, false,
	 * 		conniunction, alternative and negation.
	 */
	private static AbstractFormula getSampleFormula(int size, int seed) {
		seed %= 1000000;
		seed++;
		if (size <= 0) {
			switch (seed % 2) {
			case 0: return Predicate0Ar.FALSE;
			case 1: return Predicate0Ar.TRUE;
			default: throw new RuntimeException("internal tests error");
			}
		}else {
			switch (seed % 3) {
			case 0: return new Formula(Code.AND, getSampleFormula(size-1, seed*5), getSampleFormula(size-1, seed*7));
			case 1: return new Formula(Code.OR, getSampleFormula(size-1, seed*11), getSampleFormula(size-1, seed*13));
			case 2: return new Formula(Code.NOT, getSampleFormula(size-1, seed*17));
			default: throw new RuntimeException("internal tests error");
			}
		}
	}
	
	private static void error(String errMsg) {
		System.out.println("Fatal error: " + errMsg);
		throw new RuntimeException(errMsg);
	}
	
	// below are some test scenarios. They can throw many
	// exception that are catched in main method.
	// An exception usually means an error in BmlLib library
	// (unless Paths are set incorrectly) and won't be
	// described in JavaDocs.
	
	/**
	 * Saves <code>bcc</code> and loads it back.
	 */
	private static void refresh() throws IOException, ClassNotFoundException,
			ReadAttributeException {
		bcc.saveToFile(Paths.tmp_path + "test\\Empty.class");
		bcc = new BCClass(Paths.tmp_path, "test.Empty");
		String cpCode = bcc.printCp();
		System.out.println(xxx);
		System.out.println(cpCode);
		String code = bcc.printCode();
		System.out.println(xxx);
		System.out.println(addLineNumbers(code));
	}

	/**
	 * Adds line numbers to given String.
	 * 
	 * @param str - multi line String.
	 * @return <code>str</code> with line numbers (starting
	 * 		from 0) at the beginning of each line.
	 */
	private static String addLineNumbers(String str) {
		String[] lines = str.split("\n");
		String code = "";
		for (int i = 0; i < lines.length; i++) {
			if (i < 100)
				code += " ";
			if (i < 10)
				code += " ";
			code += i + "|  " + lines[i] + "\n";
		}
		return code;
	}

	/**
	 * Adds some annotations to BCClass loaded from
	 * "Empty2.class" file. Deterministic. Do not change
	 * "Empty2.class" file.
	 * 
	 * @return BCClass loaded from "Empty2.class" example
	 * 		file, with some BML annotations.
	 */
	public static BCClass createSampleClass() throws ClassNotFoundException,
			ReadAttributeException {
		MLog.putMsg(MLog.PInfo, xxx);
		bcc = new BCClass(Paths.path, "test.Empty2");
		BCMethod m1 = bcc.getMethod(2);
		BCMethod m2 = bcc.getMethod(3);
		AbstractFormula f0 = getSampleFormula(2, 0);
		SingleAssert a0 = new SingleAssert(m1, 0, -1, f0);
		m1.addAttribute(a0);
		AbstractFormula f1 = getSampleFormula(5, 0);
		SingleAssert a1 = new SingleAssert(m2, 58, -1, f1);
		m2.addAttribute(a1);
		AbstractFormula f2 = getSampleFormula(5, 1);
		SingleAssert a2 = new SingleAssert(m2, 58, -1, f2);
		m2.addAttribute(a2);
		AbstractFormula f3 = getSampleFormula(5, 2);
		SingleAssert a3 = new SingleAssert(m2, 46, -1, f3);
		m2.addAttribute(a3);
		AbstractFormula f4 = getSampleFormula(5, 3);
		SingleAssert a4 = new SingleAssert(m2, 58, -1, f4);
		m2.addAttribute(a4);
		MethodSpecification ms = new MethodSpecification(m2);
		m2.setMspec(ms);
		ClassInvariant civ = new ClassInvariant(bcc);
		bcc.addAttribute(civ);
		return bcc;
	}

	public static BCClass createSampleClass2()
			throws ClassNotFoundException,
			ReadAttributeException {
		bcc = new BCClass(Paths.path, "test.Empty");
		bcc.addAttribute(new ClassInvariant(bcc, getSampleFormula(4, 0)));
		for (int i=0; i<bcc.getMethodCount(); i++) {
			BCMethod m = bcc.getMethod(i);
			InstructionHandle[] ihs = m.getInstructions().getInstructionHandles();
			m.setMspec(new MethodSpecification(m, getSampleFormula(2*i+1, 0), new SpecificationCase[0]));
			m.addAttribute(new SingleAssert(m, ihs[0], 0, getSampleFormula(2*i+2, 0)));
			m.addAttribute(new SingleAssert(m, ihs[2], 0, getSampleFormula(2*i+2, 1)));
			m.addAttribute(new SingleAssert(m, ihs[2], 4, getSampleFormula(2*i+2, 2)));
			m.addAttribute(new SingleAssert(m, ihs[2], 0, getSampleFormula(2*i+2, 3)));
		}
		return bcc;
	}
	
	/**
	 * @return newly created simple quantified formula.
	 */
	private static AbstractFormula sampleQuantifiedFormula() {
		QuantifiedFormula f = new QuantifiedFormula(Code.FORALL_WITH_NAME);
		BoundVar bv = new BoundVar(JavaType.JavaInt, 0, f, "a");
		f.addVariable(bv);
		f.setFormula(new Predicate2Ar(Code.LESS, bv, new NumberLiteral(10)));
		return f;
	}

	/**
	 * A simple test scenario.
	 */
	private static void addRemoveTest() throws IOException,
			ClassNotFoundException, ReadAttributeException,
			RecognitionException {
		System.out.println(xxx);
		bcc = new BCClass(Paths.path, "test.Empty");
		bcc.setInvariant(new ClassInvariant(bcc));
		BCMethod m = bcc.getMethod(1);
		SpecificationCase[] sc = { new SpecificationCase(m, Predicate0Ar.TRUE,
				Predicate0Ar.FALSE) };
		m.setMspec(new MethodSpecification(m, Predicate0Ar.TRUE, sc));
		SingleAssert olda = (SingleAssert) m.getAmap().addAttribute(1, 8, 3);
		m.getAmap().addAttribute(1, 5, 0);
		SingleAssert sa = (SingleAssert) m.getAmap().addAttribute(1, 8, 2);
		sa.parse("\\assert false");
		AbstractFormula af = generateRandomFormula(5);
		SingleAssert newa = new SingleAssert(m, null, -1, af);
		olda.replaceWith(newa);
		SingleAssert a2 = new SingleAssert(m, 8, -1, Predicate0Ar.TRUE);
		m.getAmap().addAttribute(a2, 2);
		System.out.println("minor = " + newa.getMinor());
		if (newa.getMinor() != 4)
			throw new RuntimeException("error (minor != 4)");
		refresh();
		CodeSearch.ComputeAttributeLines(bcc);
		BCPrintableAttribute[] all = bcc.getAllAttributes(AType.C_ALL);
		for (int i = 0; i < all.length; i++)
			all[i].remove();
		refresh();
	}
	
	/**
	 * Another test scenario, for parsing large fragments
	 * of code.
	 */
	private static void attributeSearchTest() throws ClassNotFoundException,
			ReadAttributeException {
		String change1 = "| false) && (true |";
		String change2 = "ue || false))))\n * \\assert ((true ==> true) && (false || true";
		String change3 = "    ~(~(~false))) &&\n"+
		" *    ((false && false || ~false) &&\n"+
		" *        (false && true || ~false) ||\n"+
		" *      ~(~(~false)))\n"+
		" */\n"+
		"46:   getstatic		test.Empty2.l I (10)\n"+
		"49:   invokevirtual	java.lang.StringBuilder.append (I)Ljava/lang/StringBuilder; (42)\n"+
		"52:   invokevirtual	java.lang.StringBuilder.toString ()Ljava/lang/String; (51)\n"+
		"55:   invokevirtual	java.io.PrintStream.println (Ljava/lang/String;)V (55)\n"+
		"/*\n"+ 
		" * \\assert ((false || false) &&\n"+
		" *          (false || false) || ~false) &&\n"+
		" *      ((false |";
		String change4 = "ad\n65:   ireturn\n\n/* \\requires false */\npublic static void main(String[] args)\n0";
		bcc = createSampleClass();
		String code = bcc.printCode();
		System.out.println(addLineNumbers(code));
		System.out.println(xxx);
		CodeFragment cf = new CodeFragment(bcc, code);
		String[] lines = code.split("\n");
		for (int i=0; i<lines.length; i++)
			System.out.println(i+": "+CodeFragment.getKeyword(lines[i]));
//		System.out.println(xxx);
//		for (int i=0; i<lines.length; i++)
//			System.out.println("" + i + ": "
//				+ cf.where(i, 3).toString());
		System.out.println(xxx);
		System.out.println("total code length: " + code.length());
		for (int i=1; i<lines.length; i++) {
			int off = CodeFragment.getLineOffset(code, i);
			if (CodeFragment.getLineOfOffset(code, off) != i)
				error("offset error ("+i+"b)");
			if (CodeFragment.getLineOfOffset(code, off-1) != i-1)
				error("offset error ("+i+"e)");
		}
		cf = new CodeFragment(bcc, code);
		System.out.println("### stage 0");
		cf.addChange(2535, 20, change1);
		cf.addChange(2537, 5, "true");
		cf.addChange(2552, 2, "==>");
		cf.addChange(2528, 10, "true || t");
		cf.addChange(2528, 30, "true && fal");
		cf.addChange(2527, 0, "(0<1) || ");
		cf.addChange(2549, 4, "e && true) |");
		cf.performChanges();
		System.out.println(cf.toString());
		cf = new CodeFragment(bcc, code);
		System.out.println("### stage 1");
		cf.modify(2535, 20, change1);
		System.out.println(cf.toString());
		if (!cf.isCorrect())
			error("test 1: code replace failed!");
//		cf = new CodeFragment(bcc, code);
//		System.out.println("### stage 2");
//		cf.modify(2635, 50, change2);
////		if (!cf.isCorrect())
////			error("test 2: code replace failed!");
//		cf = new CodeFragment(bcc, code);
//		System.out.println("### stage 3");
//		cf.modify(2035, 500, change3);
////		if (!cf.isCorrect())
////			error("test 3: code replace failed!");
//		cf = new CodeFragment(bcc, code);
//		System.out.println("### stage 4");
//		cf.modify(1116, 79, change4);
////		if (!cf.isCorrect())
////			error("test 4: code replace failed!");
//		cf = new CodeFragment(bcc, code);
//		System.out.println("### stage 5");
//		cf.modify(307, 2, "<=!=>");
////		if (!cf.isCorrect())
////		error("test 5: code replace failed!");
	}

	/**
	 * A prettyPrinter test. Loads "Empty.class" file and
	 * adds an large assert to it, then displays it.
	 */
	private static void pp_test() throws ClassNotFoundException,
			ReadAttributeException, IOException {
		// wether assert formula should be generated and saved
		// to file, or loaded from it.
		final boolean generate = true;
		// file name to save assert formula to / load it from.
		final String fname = "c04";
		if (generate) {
			bcc = new BCClass(Paths.path, "test.Empty");
			BCMethod m = bcc.getMethod(1);
			AbstractFormula f = generateRandomFormula(5);
			// AbstractFormula f = getSampleFormula();
			// AbstractFormula f = sampleQuantifiedFormula();
			SingleAssert sa = new SingleAssert(m, 8, 3, f);
			m.addAttribute(sa);
			bcc.saveToFile(Paths.tmp_path + "test\\" + fname + ".class");
		} else {
			bcc = new BCClass(Paths.tmp_path, "test." + fname);
		}
		String code = bcc.printCode();
		System.out.println(xxx);
		System.out.println(code);
	}

	private static void singleTest(String from, String to) {
		singleTest(from, to, -1);
	}

	private static void singleTest(String from, String to, int hash) {
		int cfrom = code.indexOf(from) + from.length();
		int cto = code.indexOf(to, cfrom);
		String newCode = "XXX"+code.substring(cfrom, cto);
		newCode = newCode.toUpperCase(); // changes sth.
		singleTest(from, to, hash, newCode);
	}

	private static void singleTest(String from, String to, int hash, String newCode) {
		System.out.println("************ test nr " + test_nr + " ************");
		int oldMask = MLog.mask;
		MLog.mask = MLog.PERRORS;
		CodeFragment cf = new CodeFragment(bcc, code);
		int cfrom = code.indexOf(from) + from.length();
		int cto = code.indexOf(to, cfrom);
		cf.modify(cfrom, cto - cfrom, newCode);
		int h = cf.hash();
		System.out.print("hash = " + h);
		if (h == hash) {
			System.out.println(" (ok)");
		} else {
			if (hash == -1) {
				System.out.println(" (not set yet)");
			} else {
				System.out.println(" (should be " + hash + ")");
			}
			MLog.mask = MLog.PNORMAL;
			cf = new CodeFragment(bcc, code);
			cf.modify(cfrom, cto - cfrom, newCode);
			System.out.println(cf.toString());
		}
//		if (!cf.isCorrect())
//			error("Test " + test_nr + ": code replace failed");
		MLog.mask = oldMask;
		test_nr++;
	}
	
	private static void attributeSearchTest2()
			throws ClassNotFoundException,
			ReadAttributeException {
		bcc = createSampleClass2();
		code = bcc.printCode();
		System.out.println(code);
		System.out.println(xxx);
		System.out.println("length: " + code.length());
		singleTest("~true", " && true || ~true) ||", -1);
//		singleTest("\\class", "))", 810);
//		singleTest("\\req", "| false", -1);
//		singleTest("\\a", "~tr", 146);
//		singleTest("~(~f", "e)", 50);
//		singleTest("rt (tr", "ue) &", 169);
//		singleTest("*    ~(~(~", "))", 505);
//		singleTest(" *    ~(~f", "e)", 941);
//		singleTest("~(~(~(~", "sse", 309);
//		singleTest("/*", "*/", 629);
//		singleTest(")\n/*", "*/", 145);
//		singleTest("assert", "~(~", 295);
//		singleTest("ldc", "~", 732);
//		singleTest("requires", "true", 462);
//		singleTest("res (", "e))", 985);
//		singleTest("~(~false", "\\req", 785);
//		singleTest("invariant", "requires", 82);
//		singleTest("rt false", " && (", 301, "");
//		singleTest("~(~(~(~", "\\a", 385, "false)))\n\\assert true\n * ");
//		singleTest("(20)", "\n3:", 394, "\n/* \\assert false");
//		singleTest("(20)", "\n3:", 354, "\n/* \\assert false */");
//		singleTest("()\n", "\n0:", -1, "");
//		singleTest("/*", "*/", -1, "");
	}
	
	/**
	 * Main method for running these tests.
	 * 
	 * @param args - unused.
	 */
	public static void main(String[] args) {
		try {
//			addRemoveTest();
			attributeSearchTest();
//			attributeSearchTest2();
//			pp_test();
			System.out.println("done.");
		} catch (Exception e) {
			System.out.println("error!");
			e.printStackTrace();
		}
	}

}
