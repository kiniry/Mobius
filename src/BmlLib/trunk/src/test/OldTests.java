package test;

import java.io.IOException;
import java.util.Random;

import org.antlr.runtime.RecognitionException;

import annot.attributes.AType;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.ClassInvariant;
import annot.attributes.MethodSpecification;
import annot.attributes.SingleAssert;
import annot.attributes.SpecificationCase;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
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
		System.out.println(xxx);
		bcc = new BCClass(Paths.path, "test.Empty2");
		BCMethod m2 = bcc.getMethod(3);
		SingleAssert a1 = new SingleAssert(m2, 58, -1);
		m2.addAttribute(a1);
		SingleAssert a2 = new SingleAssert(m2, 58, -1);
		m2.addAttribute(a2);
		SingleAssert a3 = new SingleAssert(m2, 46, -1);
		m2.addAttribute(a3);
		SingleAssert a4 = new SingleAssert(m2, 58, -1);
		m2.addAttribute(a4);
		MethodSpecification ms = new MethodSpecification(m2);
		m2.setMspec(ms);
		ClassInvariant civ = new ClassInvariant(bcc);
		bcc.addAttribute(civ);
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
	 * Another simple test scenario.
	 */
	private static void addRemoveTest2() throws ClassNotFoundException,
			ReadAttributeException, RecognitionException, IOException {
		String code = createSampleClass().printCode();
		System.out.println(xxx);
		int[] w = CodeSearch.where(code, 104);
		System.out.println("m=" + w[0] + "  p=" + w[1] + "  m=" + w[2] + "  l="
				+ w[3]);
		BCPrintableAttribute pa = CodeSearch
				.findAttributeAtLine(bcc, code, 104);
		System.out.println(pa.getClass().toString());
		String str = Parsing.purge("/* \\requires false */");
		System.out.println("|" + str + "|");
		BCMethod m = bcc.getMethod(w[0]);
		pa.parse(str);
		System.out.println(xxx);
		code = bcc.printCode();
		System.out.println(addLineNumbers(code));
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

	/**
	 * Main method for running these tests.
	 * 
	 * @param args - unused.
	 */
	public static void main(String[] args) {
		try {
			addRemoveTest();
			addRemoveTest2();
			pp_test();
			System.out.println("done.");
		} catch (Exception e) {
			System.out.println("error!");
			e.printStackTrace();
		}
	}

}
