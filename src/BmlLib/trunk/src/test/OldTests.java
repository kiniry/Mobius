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

public class OldTests {

	static public final boolean goGenerateRandomQuantifiedFormulas = false;
	
	static public String xxx = "################################################################################";
	private static BCClass bcc;
	private static Random random;

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

	private static AbstractFormula generateRandomFormula(int size) {
		return grf(size, 0.5, 0);
	}

	private static AbstractFormula grf(int size, double w, int ind) {
		int[] connectors = { Code.TRUE, Code.FALSE, Code.NOT, Code.AND,
				Code.OR, Code.IMPLIES, Code.FORALL_WITH_NAME };
		String[] names = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j" };
		int n = connectors.length;
		if (!goGenerateRandomQuantifiedFormulas)
			n--;
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
			QuantifiedFormula qf = new QuantifiedFormula(code);
			int bvc = rand() % 3 + 1;
			for (int i = 0; i < bvc; i++) {
				qf.addVariable(new BoundVar(JavaType.JavaInt, ind, qf,
						names[ind % names.length]));
				ind++;
			}
			qf.setFormula(grf(s, w + 0.1, ind));
			return qf;
		default:
			throw new RuntimeException("error in generateRandomFormula");
		}
	}

	private static void refresh(String clName) throws IOException,
			ClassNotFoundException, ReadAttributeException {
		bcc.saveToFile(Paths.tmp_path + clName + ".class");
		bcc = new BCClass(Paths.tmp_path + clName + ".class", "test.Empty");
		String cpCode = bcc.printCp();
		System.out.println(xxx);
		System.out.println(cpCode);
		String code = bcc.printCode();
		System.out.println(xxx);
		System.out.println(addLineNumbers(code));
	}

	private static void addRemoveTest() throws IOException,
			ClassNotFoundException, ReadAttributeException {
		System.out.println(xxx);
		bcc = new BCClass(Paths.path, "test.Empty");
		bcc.invariant = new ClassInvariant(bcc);
		BCMethod m = bcc.methods[1];
		SpecificationCase[] sc = { new SpecificationCase(m, Predicate0Ar.TRUE,
				Predicate0Ar.FALSE) };
		m.mspec = new MethodSpecification(m, Predicate0Ar.TRUE, sc);
		SingleAssert olda = (SingleAssert) m.amap.addAttribute(1, 8, 3);
		m.amap.addAttribute(1, 5, 0);
		SingleAssert sa = (SingleAssert) m.amap.addAttribute(1, 8, 2);
		sa.formula = Predicate0Ar.FALSE;
		AbstractFormula af = generateRandomFormula(5);
		SingleAssert newa = new SingleAssert(m, null, -1, af);
		olda.replaceWith(newa);
		SingleAssert a2 = new SingleAssert(m, 8, -1, Predicate0Ar.TRUE);
		m.amap.addAttribute(a2, 2);
		System.out.println("minor = " + newa.minor);
		if (newa.minor != 4)
			throw new RuntimeException("error (minor != 4)");
		refresh("tmp1");
		CodeSearch.ComputeAttributeLines(bcc);
		BCPrintableAttribute[] all = bcc.getAllAttributes(AType.C_ALL);
		for (int i = 0; i < all.length; i++)
			all[i].remove();
		refresh("tmp2");
	}

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

	public static BCClass createSampleClass() throws ClassNotFoundException,
			ReadAttributeException {
		System.out.println(xxx);
		bcc = new BCClass(Paths.path, "test.Empty2");
		BCMethod m2 = bcc.methods[3];
		SingleAssert a1 = new SingleAssert(m2, 58, -1);
		m2.addAttribute(a1);
		SingleAssert a2 = new SingleAssert(m2, 58, -1);
		m2.addAttribute(a2);
		SingleAssert a3 = new SingleAssert(m2, 46, -1);
		m2.addAttribute(a3);
		SingleAssert a4 = new SingleAssert(m2, 58, -1);
		m2.addAttribute(a4);
		MethodSpecification ms = new MethodSpecification(m2);
		m2.mspec = ms;
		ClassInvariant civ = new ClassInvariant(bcc);
		bcc.addAttribute(civ);
		// String cp = bcc.printCp();
		// String code = bcc.printCode();
		// System.out.println(xxx);
		// System.out.println(cp);
		// System.out.println(xxx);
		// System.out.println(addLineNumbers(code));
		return bcc;
	}

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
		BCMethod m = bcc.methods[w[0]];
		pa.parse(bcc, m, m.findAtPC(w[1]), w[2], str);
		System.out.println(xxx);
		code = bcc.printCode();
		System.out.println(addLineNumbers(code));
	}

	private static AbstractFormula getSampleFormula() {
		return new Formula(4, new Formula(2, new Formula(2, new Formula(3,
				new Predicate0Ar(true), new Predicate0Ar(true)), new Formula(3,
				new Predicate0Ar(true), new Predicate0Ar(false))), new Formula(
				5, new Formula(3, new Predicate0Ar(false), new Predicate0Ar(
						true)))), new Formula(4, new Formula(5, new Formula(2,
				new Predicate0Ar(true), new Predicate0Ar(true))), new Formula(
				4, new Formula(4, new Predicate0Ar(false), new Predicate0Ar(
						false)), new Formula(5, new Predicate0Ar(true)))));
	}

	private static AbstractFormula sampleQuantifiedFormula() {
		QuantifiedFormula f = new QuantifiedFormula(Code.FORALL_WITH_NAME);
		BoundVar bv = new BoundVar(JavaType.JavaInt, 0, f, "a");
		f.addVariable(bv);
		f.setFormula(new Predicate2Ar(Code.LESS, bv, new NumberLiteral(10)));
		return f;
	}

	private static void pp_test() throws ClassNotFoundException,
			ReadAttributeException {
		bcc = new BCClass(Paths.path, "test.Empty");
		BCMethod m = bcc.methods[1];
		AbstractFormula f = generateRandomFormula(8);
		// AbstractFormula f = getSampleFormula();
		// AbstractFormula f = sampleQuantifiedFormula();
		SingleAssert sa = new SingleAssert(m, 8, 3, f);
		m.addAttribute(sa);
		String code = bcc.printCode();
		System.out.println(xxx);
		System.out.println(code);
	}

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
