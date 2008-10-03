package test;

import java.io.IOException;
import java.util.Random;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.attributes.AType;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.ClassInvariant;
import annot.attributes.MethodSpecification;
import annot.attributes.SingleAssert;
import annot.attributes.SingleLoopSpecification;
import annot.attributes.SpecificationCase;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.FieldRef;
import annot.bcexpression.LocalVariable;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Formula;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.formula.Predicate2Ar;
import annot.bcexpression.formula.QuantifiedFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.util.DesugarWalker;
import annot.bcexpression.util.ExpressionWalker;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.CodeFragment;
import annot.textio.CodePosition;
import annot.textio.CodeSearch;

/**
 * Manual tests for BmlLib library. After running some
 * of this scenarios, tester should take a look to the console
 * and check if all displayed values are as expected.
 * Some of this tests are undeterministic, so sometimes
 * it's not possible to memorize all results and check if one
 * displayed is equal to the correct one, stored eg. in a file.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public final class ManualTests {

  /**
   * A class used for tests.
   */
  private static BCClass bcc;

  /**
   * Test class's (bcc's) code.
   */
  private static String code;

  /**
   * Number of failed tests so far.
   */
  private static int errc = 0;

  /**
   * If a flag above is on, this flag controls whether
   * random formula generator should generate only
   * 3args quantified formulas (with exactly one
   * implication at the root) or not.
   */
  public static final boolean go3argQuantifiersGenerated = true;

  /**
   * Disables lowering verbosity level on first test's run,
   * for debugging test cases that crashes (that throws
   * RuntimeExceptions).
   */
  public static final boolean goDisplayAllMessages = false;

  /**
   * whether random formula generator should also generate
   * ugly, unproportial quantified formula to make it's
   * formatting more difficult, or not.
   */
  public static final boolean goGenerateRandomQuantifiedFormulas = true;

  /**
   * Set it to true to ignore save / load error
   * in the next test.
   */
  private static boolean ignoreSaveLoadFailure = false;

  /**
   * A random stream.
   */
  private static Random random;

  /**
   * Current test's number.
   */
  private static int test_nr = 0;

  /**
   * Simple line hashes, for separating data printed to
   * the console.
   */
  public static final String xxx = "################################################################################";

  /**
   * Adds line numbers to given String.
   *
   * @param str - multi line String.
   * @return <code>str</code> with line numbers (starting
   *     from 0) at the beginning of each line.
   */
  private static String addLineNumbers(final String str) {
    final String[] lines = str.split("\n");
    String code = "";
    for (int i = 0; i  <  lines.length; i++) {
      if (i  <  100) {
        code += " ";
      }
      if (i  <  10) {
        code += " ";
      }
      code += i + "|  " + lines[i] + "\n";
    }
    return code;
  }

  /**
   * A simple test scenario.
   */
  @SuppressWarnings("deprecation")
  private static void addRemoveTest() throws IOException,
      ClassNotFoundException, ReadAttributeException, RecognitionException {
    System.out.println(xxx);
    bcc = new BCClass(Paths.path, "test.Empty");
    bcc.setInvariant(new ClassInvariant(bcc, true));
    final BCMethod m = bcc.getMethod(1);
    final SpecificationCase[] sc = { new SpecificationCase(
                                                           m,
                                                           new Predicate0Ar(
                                                                            true),
                                                           null,
                                                           new Predicate0Ar(
                                                                            false),
                                                           null) };
    m.setMspec(new MethodSpecification(m, sc));
    final SingleAssert olda = (SingleAssert) m.getAmap().addAttribute(1, 8, 3);
    m.getAmap().addAttribute(1, 5, 0);
    final SingleAssert sa = (SingleAssert) m.getAmap().addAttribute(1, 8, 2);
    sa.parse("\\assert false");
    final AbstractFormula af = generateRandomFormula(5);
    final SingleAssert newa = new SingleAssert(m, null, -1, af);
    olda.replaceWith(newa);
    final SingleAssert a2 = new SingleAssert(m, 8, -1, new Predicate0Ar(true));
    m.getAmap().addAttribute(a2, 2);
    System.out.println("minor = " + newa.getMinor());
    if (newa.getMinor() != 4) {
      throw new RuntimeException("error (minor != 4)");
    }
    refresh();
    CodeSearch.ComputeAttributeLines(bcc);
    code = bcc.printCode();
    final int clength = code.split("\n").length;
    int hash = 0;
//    for (int i = 0; i  <  23; i++) {
//      final int up = CodeFragment.goUp(code, i);
//      final int down = CodeFragment.goDown(code, i);
//      hash += 3 * i * up + 7 * i * down;
//    }
//    if (hash % 1000 != 947) {
//      for (int i = 0; i  <  clength; i++) {
//        final int up = CodeFragment.goUp(code, i);
//        final int down = CodeFragment.goDown(code, i);
//        System.out.println("line " + i + " ~~ >  (" + up + ", " + down + ")");
//        if (up  >  i || down  <  i) {
//          error("goUp / goDown error");
//        }
//      }
//      System.out.println("hash=" + hash % 1000);
//    }
    final BCPrintableAttribute[] all = bcc.getAllAttributes(AType.C_ALL);
    for (int i = 0; i  <  all.length; i++) {
      all[i].remove();
    }
//    refresh();
  }

  /**
   * A test case for {@link CodeFragment} class. Contains
   * diffrent edit scenarios (replacing one fragment
   * (substring) of bytecode with another), both correct
   * and incorrect, to be parsed.
   */
  private static void codeReplaceTest() throws ClassNotFoundException,
      ReadAttributeException {
    bcc = createSampleClass2();
    code = bcc.printCode();
    final int noChange = CodePosition.StrHash(code) % 1000;
    System.out.println(code);
    System.out.println(xxx);
    System.out.println("length: " + code.length());
    errc = 0;
    replaceTest("~true", " && true || ~true) ||", 554, 856, true);
    replaceTest("\\class", "))", 980, 765, true);
    replaceTest("requi", "| false", 565, 480, true);
    replaceTest("\\a", "~tr", 386, 209, true);
    replaceTest("~(~f", "e)", 593, noChange, true);
    replaceTest("rt (tr", "ue) &", 905, noChange, true);
    replaceTest("*    ~(~(~", "))", 753, 718, true);
    replaceTest(" *    ~(~f", "e)", 479, noChange, true);
    replaceTest("~(~(~(~", "sse", 129, 42, true);
    replaceTest("/*", "*/", 735, 765, true);
    replaceTest(")\n/*", "*/", 102, 923, true);
    replaceTest("assert", "~(~", 85, 923, true);
    replaceTest("ldc", "~", 47, noChange, true);
    replaceTest("requires", "true", 536, 599, true);
    replaceTest("res (", "e))", 183, 25, true);
    replaceTest("~(~false", "requi", 542, 517, true);
    replaceTest("invariant", "requires", 654, 765, true);
    replaceTest("rt false", " && (", 191, 830, true, "");
    //replaceTest("~(~(~(~", "\\a", 574, 431, true,
    //            "false)))\n\\assert true\n * ");
    replaceTest("(20)", "\n3:", 638, noChange, false, "\n/* \\assert false");
    replaceTest("(20)", "\n3:", 286, 993, true, "\n/* \\assert false */");
    replaceTest("(20)", "\n3:", 442, 993, true, "\n  /* \\assert false */  ");
    replaceTest("()\n", "\n0:", 160, 535, true, "");
    replaceTest("/*", "*/", 216, 280, true, "");
    replaceTest("/*", "\n", 350, noChange, true, "");
    replaceTest("/*", "*/", 680, 280, true, "  ");
    replaceTest("Empty\n\n", "\npublic", 734, 383, true, ""); //XXX changed after alx's BCMethod.printCode() modification.
    replaceTest("V (28)\n", "8:", 655, 138, true,
                "/* \\assert forall int a; a  >  0 */\n");
    // TODO current BML-annotated .class file format don't support
    // storeing minor munber, so diffrent bytecodes are equal after saving.
    ignoreSaveLoadFailure = true;
    replaceTest("(26)\n/*@ \n @ ", " @ assert ((", 917, 65, true,
                "loop specification\n @   modifies \\nothing\n");
    ignoreSaveLoadFailure = true;
    replaceTest(
                "(26)\n/*@ \n @ ",
                " @ assert ((",
                200,
                879,
                true,
                "\\loop specification\n *   \\modifies nothing\n *   \\invariant true\n *   \\decreases 2 + 2\n");
    replaceTest("p", null, 899, noChange, false, "");
    replaceTest("p", null, 195, 298, true);
    System.out.println("code replace tests completed.");
    if (errc  >  0) {
      System.out.println("FAILURES: " + errc + " out of " + test_nr
                         + " tests failed!");
    } else {
      System.out.println("SUCCESS: all " + test_nr + " tests passed");
    }
  }

  /**
   * Adds some annotations to BCClass loaded from
   * "Empty2.class" file. Deterministic. Do not changes
   * "Empty2.class" file.
   *
   * @return BCClass loaded from "Empty2.class" example
   *     file, with some BML annotations.
   */
  @SuppressWarnings("deprecation")
  public static BCClass createSampleClass() throws ClassNotFoundException,
      ReadAttributeException {
    MLog.putMsg(MLog.LEVEL_PINFO, xxx);
    bcc = new BCClass(Paths.path, "test.Empty2");
    final BCMethod m1 = bcc.getMethod(2);
    final BCMethod m2 = bcc.getMethod(3);
    final AbstractFormula f0 = getSampleFormula(2, 0);
    final SingleAssert a0 = new SingleAssert(m1, 0, -1, f0);
    m1.addAttribute(a0);
    final AbstractFormula f1 = getSampleFormula(5, 0);
    final SingleAssert a1 = new SingleAssert(m2, 58, -1, f1);
    m2.addAttribute(a1);
    final AbstractFormula f2 = getSampleFormula(5, 1);
    final SingleAssert a2 = new SingleAssert(m2, 58, -1, f2);
    m2.addAttribute(a2);
    final AbstractFormula f3 = getSampleFormula(5, 2);
    final SingleAssert a3 = new SingleAssert(m2, 46, -1, f3);
    m2.addAttribute(a3);
    final SingleLoopSpecification sls1 = new SingleLoopSpecification(m2, m2
        .findAtPC(52), -1, null, null, null);
    m2.addAttribute(sls1);
    final AbstractFormula f4 = getSampleFormula(5, 3);
    final SingleAssert a4 = new SingleAssert(m2, 58, -1, f4);
    m2.addAttribute(a4);
    final MethodSpecification ms = new MethodSpecification(m2);
    m2.setMspec(ms);
    final ClassInvariant civ = new ClassInvariant(bcc, true);
    bcc.addAttribute(civ);
    return bcc;
  }

  /**
   * Another sample class, with few code and lots
   * of anotations. Adds many annotations to BCClass
   * loaded from "Empty.class" file. Deterministic.
   * Do not changes "Empty.class" file.
   *
   * @return BCClass loaded from "Empty.class" example
   *     file, with many (11) BML annotations.
   */
  public static BCClass createSampleClass2() throws ClassNotFoundException,
      ReadAttributeException {
    bcc = new BCClass(Paths.path, "test.Empty");
    bcc.addAttribute(new ClassInvariant(bcc, getSampleFormula(4, 0), true));
    for (int i = 0; i  <  bcc.getMethodCount(); i++) {
      final BCMethod m = bcc.getMethod(i);
      final InstructionHandle[] ihs = m.getInstructions()
          .getInstructionHandles();
      SpecificationCase[] specCase = new SpecificationCase[1];
      specCase[0] = new SpecificationCase(m, getSampleFormula(2 * i + 1, 0),
                                          null, null, null);
      m.setMspec(new MethodSpecification(m, specCase));
      m.addAttribute(new SingleAssert(m, ihs[0], 0, getSampleFormula(2 * i + 2,
                                                                     0)));
      m.addAttribute(new SingleAssert(m, ihs[2], 0, getSampleFormula(2 * i + 2,
                                                                     1)));
      m.addAttribute(new SingleAssert(m, ihs[2], 4, getSampleFormula(2 * i + 2,
                                                                     2)));
      m.addAttribute(new SingleAssert(m, ihs[2], 0, getSampleFormula(2 * i + 2,
                                                                     3)));
    }
    return bcc;
  }

  // below are some test scenarios. They can throw many
  // exception that are catched in main method.
  // An exception usually means an error in BmlLib library
  // (unless Paths are set incorrectly) and won't be
  // described in JavaDocs.

  /**
   * Test for expression's desugaring. Creates sample class,
   * shows it's bytecode, launches desugar and shows modified
   * bytecode.
   */
  private static void desugarTest() throws ClassNotFoundException,
      ReadAttributeException {
    bcc = createSampleClass2();
    String code = bcc.printCode();
    System.out.println("Old code:\n" + code);
    System.out.println(xxx);
    final int changes = bcc.iterate(true, new DesugarWalker()).getChanges();
    code = bcc.printCode();
    System.out.println(xxx);
    System.out.println("New code:\n" + code);
    System.out.println("performed " + changes + " changes.");
  }

  /**
   * Displays error message to stdout and throws
   * RuntimeException.
   *
   * @param errMsg - error message to be displayed.
   */
  private static void error(final String errMsg) {
    System.out.println("Fatal error: " + errMsg);
    throw new RuntimeException(errMsg);
  }

  /**
   * Generates a random formula, of size less or equal than
   * given value.
   *
   * @param size - maximum size of generaed formula.
   * @return random formula with basic predicates,
   *     formulas and quantifiers (but without bound
   *     variables except it's declarations at quantifiers).
   */
  private static AbstractFormula generateRandomFormula(final int size) {
    return grf(size, 0.5, 0);
  }

  /**
   * Creates a pseudo-random formula. Each call of this
   * function with the same parameters will give the same
   * formula (similar, but not the same object).
   *
   * @param size - depth of generated formula,
   * @param seed - another parameter,
   * @return a formula, containing (at most) true, false,
   *     conniunction, alternative and negation.
   */
  private static AbstractFormula getSampleFormula(final int size, int seed) {
    seed %= 1000000;
    seed++;
    if (size  <= 0) {
      switch (seed % 2) {
      case 0:
        return new Predicate0Ar(false);
      case 1:
        return new Predicate0Ar(true);
      default:
        throw new RuntimeException("internal tests error");
      }
    } else {
      switch (seed % 3) {
      case 0:
        return new Formula(Code.AND, getSampleFormula(size - 1, seed * 5),
                           getSampleFormula(size - 1, seed * 7));
      case 1:
        return new Formula(Code.OR, getSampleFormula(size - 1, seed * 11),
                           getSampleFormula(size - 1, seed * 13));
      case 2:
        return new Formula(Code.NOT, getSampleFormula(size - 1, seed * 17));
      default:
        throw new RuntimeException("internal tests error");
      }
    }
  }

  /**
   * Generates a random formula.
   *
   * @param size - maximum formula depth,
   * @param w - width (?) of generated formula,
   * @param ind - index of next bound variable names.
   * @return random formula.
   */
  private static AbstractFormula grf(final int size, double w, int ind) {
    final int[] connectors = { Code.TRUE, Code.FALSE, Code.NOT, Code.AND,
                              Code.OR, Code.IMPLIES, Code.FORALL_WITH_NAME,
                              Code.EXISTS_WITH_NAME };
    final String[] names = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j" };
    int n = connectors.length;
    if (!goGenerateRandomQuantifiedFormulas) {
      n -= 2;
    }
    int r = rand() % n;
    if (w  >  1) {
      w = 1;
    }
    r = (int) (r * w + (n - 1) * (1.0 - w));
    if (size  <= 0) {
      r = r % 2;
    }
    final int code = connectors[r];
    final int s = size - 1;
    switch (code) {
    case Code.AND:
    case Code.OR:
    case Code.IMPLIES:
      return new Formula(code, grf(s, w + 0.1, ind), grf(s, w + 0.1, ind));
    case Code.NOT:
      return new Formula(code, grf(s, w + 0.1, ind));
    case Code.TRUE:
      return new Predicate0Ar(true);
    case Code.FALSE:
      return new Predicate0Ar(false);
    case Code.FORALL_WITH_NAME:
    case Code.EXISTS_WITH_NAME:
      final QuantifiedFormula qf = new QuantifiedFormula(code);
      final int bvc = rand() % 3 + 1;
      for (int i = 0; i  <  bvc; i++) {
        qf.addVariable(new BoundVar(JavaBasicType.JavaInt, ind, qf,
                                    names[ind % names.length]));
        ind++;
      }
      AbstractFormula f;
      if (go3argQuantifiersGenerated) {
        final AbstractFormula f1 = grf(s, w + 0.1, ind);
        final AbstractFormula f2 = grf(s, w + 0.1, ind);
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
   * Test of expression's iterator.
   */
  private static void iterTest() throws ClassNotFoundException,
      ReadAttributeException {
    bcc = createSampleClass2();
    final BCPrintableAttribute[] all = bcc.getAllAttributes();
    final BCExpression expr = ((ClassInvariant) all[0]).getInvariant();
    final BMLConfig conf = new BMLConfig();
    System.out.println(xxx);
    System.out.println(expr.printLine(conf, "old expr: "));
    //TODO test iterator.
    final myInt changes = new myInt();
    expr.iterate(false, new ExpressionWalker() {
      /**
       * replaces a && b with ~(a || ~b)
       */
      @Override
      public void iter(final BCExpression parent, final BCExpression expr) {
        if (expr.getConnector() == Code.AND) {
          expr.replaceWith(new Formula(Code.NOT,
                                       new Formula(Code.OR,
                                                   new Formula(Code.NOT, expr
                                                       .getSubExpr(0)),
                                                   new Formula(Code.NOT, expr
                                                       .getSubExpr(1)))));
          changes.value++;
        }
      }
    });
    System.out.println("Performed " + changes.value + " changes");
    System.out.println(expr.printLine(conf, "new expr: "));
    System.out.println(xxx);
    System.out.println("Old code:\n" + bcc.printCode());
    System.out.println(xxx);
    //TODO test iterator.
    final BCExpression[] allExprs = bcc.getAllExpressions(false);
    for (int i = 0; i  <  allExprs.length; i++) {
      if (allExprs[i] == null) {
        System.out.println("ERROR: allExpr[" + i + "] = null");
      }
    }
    System.out.println("Found " + allExprs.length + " expressions.");
    bcc.iterate(false, new ExpressionWalker() {
      /**
       * Swaps true and false.
       */
      @Override
      public void iter(final BCExpression parent, final BCExpression expr) {
        if (expr.getConnector() == Code.TRUE) {
          expr.replaceWith(new Predicate0Ar(false));
        } else if (expr.getConnector() == Code.FALSE) {
          expr.replaceWith(new Predicate0Ar(true));
        }
      }
    });
    System.out.println("New code:\n" + bcc.printCode());
  }

  /**
   * Main method for running these tests.
   *
   * @param args - unused.
   */
  public static void main(final String[] args) {
    try {
      //      addRemoveTest();
      //codeReplaceTest();
            variableSearchTest();
      //      pp_test();
      //      iterTest();
      //      desugarTest();
      System.out.println("done.");
    } catch (final Exception e) {
      System.out.println("error!");
      e.printStackTrace();
    }
  }

  /**
   * A prettyPrinter test. Loads "Empty.class" file and
   * adds an large assert to it, then displays it.
   */
  @SuppressWarnings("deprecation")
  private static void pp_test() throws ClassNotFoundException,
      ReadAttributeException, IOException {
    // whether assert formula should be generated and saved
    // to file, or loaded from it.
    final boolean generate = true;
    // file name to save assert formula to / load it from.
    final String fname = "c04";
    if (generate) {
      bcc = new BCClass(Paths.path, "test.Empty");
      final BCMethod m = bcc.getMethod(1);
      final AbstractFormula f = generateRandomFormula(5);
      // AbstractFormula f = getSampleFormula();
      // AbstractFormula f = sampleQuantifiedFormula();
      final SingleAssert sa = new SingleAssert(m, 8, 3, f);
      m.addAttribute(sa);
      bcc.saveToFile(Paths.tmp_path + "test/" + fname + ".class");
    } else {
      bcc = new BCClass(Paths.tmp_path, "test." + fname);
    }
    final String code = bcc.printCode();
    System.out.println(xxx);
    System.out.println(code);
  }

  /**
   * @return random non-negative integer value.
   */
  private static int rand() {
    try {
      if (random == null) {
        random = Random.class.newInstance();
      }
      int ret = random.nextInt();
      return ret  >  0 ? ret : -ret;
    } catch (final Exception e) {
      e.printStackTrace();
      System.out.println("Random generator fails!");
      throw new RuntimeException("environment error!");
    }
  }

  /**
   * Saves <code>bcc</code> and loads it back.
   */
  private static void refresh() throws IOException, ClassNotFoundException,
      ReadAttributeException {
    bcc.saveToFile(Paths.tmp_path + "test/Empty.class");
    bcc = new BCClass(Paths.tmp_path, "test.Empty");
    final String code = bcc.printCode();
    System.out.println(xxx);
    System.out.println(addLineNumbers(code));
  }

  /**
   * Single test scenario for {@link CodeFragment} class.
   * Replaces given fragment of bytecode with sth correct
   * and gives it to {@link CodeFragment} class to parse it.
   * Notifies if it's behavior or parsed class changes.
   *
   * @param from - beginning of replaced fragment,
   * @param to - end of replaced fragment,
   * @param hash - model state ({@link CodeFragment#hash()}
   *     method result) of {@link CodeFragment} class
   *     after parsing given sample.
   * @see #replaceTest(String, String, int, int, boolean, String)
   */
  private static void replaceTest(final String from, final String to,
                                  final int hash, final int hash2,
                                  final boolean correct)
      throws ClassNotFoundException, ReadAttributeException {
    final int cfrom = code.indexOf(from) + from.length();
    int cto = code.length() - 1;
    if (to != null) {
      cto = code.indexOf(to, cfrom);
    }
    String newCode = code.substring(cfrom, cto);
    // changes sth.
    newCode = newCode.replaceAll("true", "TRUE");
    newCode = newCode.replaceAll("false", "true");
    newCode = newCode.replaceAll("TRUE", "false");
    replaceTest(from, to, hash, hash2, correct, newCode);
  }

  /**
   * Single test scenario for {@link CodeFragment} class.
   * Replaces given fragment of bytecode with sth correct
   * and gives it to {@link CodeFragment} class to parse it.
   * Notifies if it's behavior or parsed class changes,
   * Displaying debug messages, sample bytecode with marked
   * new (replaced) fragment, and bytecode generated
   * by BCClass after parsing (they should be the same).
   *
   * @param from - beginning of replaced fragment,
   * @param to - end of replaced fragment,
   * @param hash - model state ({@link CodeFragment#hash()}
   *     method result) of {@link CodeFragment} class
   *     after parsing given sample.
   * @see #singleTest(String, String, int, String, int)
   * @see #replaceTest(String, String, int, int, boolean, String)
   */
  private static void replaceTest(final String from, final String to,
                                  final int hash, final int hash2,
                                  final boolean correct, final String newCode)
      throws ClassNotFoundException, ReadAttributeException {
    final int oldMask = MLog.getLogMask();
    MLog.setLogMask(MLog.MASK_PERRORS);
    bcc = createSampleClass2();
    code = bcc.printCode();
    MLog.setLogMask(oldMask);
    final int cfrom = code.indexOf(from) + from.length();
    int cto = code.length() - 1;
    if (to != null) {
      cto = code.indexOf(to, cfrom);
    }
    boolean ok = singleTest(from, to, hash, newCode, correct ? 1 : -1);
    if (!ok) {
      return;
    }
    if (hash2  <  -1) {
      return;
    }
    final int ac = bcc.getAllAttributes().length;
    System.out.println("attribute count: " + ac);
    final String code1 = bcc.printCode();
    final int h = CodePosition.StrHash(code1) % 1000;
    if (h != hash2) {
      bcc = createSampleClass2();
      code = bcc.printCode();
      final CodeFragment cf = new CodeFragment(bcc, code);
      cf.addChange(cfrom, cto - cfrom, newCode);
      cf.performChanges();
      System.out.println(cf.toString());
      System.out.println("***** code after parsing: *****\n" + code1);
      if (hash2 == -1) {
        System.out.println("result hash: " + h + " (not set yet)");
      } else {
        System.out.println("result hash: " + h + " (should be " + hash2 + ")");
        errc++;
      }
    } else {
      MLog.setLogMask(MLog.MASK_PERRORS);
      bcc.saveJC();
      bcc = new BCClass(bcc.getJC());
      final String code2 = bcc.printCode();
      if (!ignoreSaveLoadFailure && !code1.equals(code2)) {
        System.out.println("ERROR: BCClass changed while saving / loading");
        System.out.println("old code:\n" + code1);
        System.out.println("new code:\n" + code2);
        errc++;
      } else {
        if (ignoreSaveLoadFailure) {
          System.out.println("Skipping save / load test.");
        }
        System.out.println("hash2 = " + hash2 + " (ok)");
      }
      MLog.setLogMask(oldMask);
    }
    ignoreSaveLoadFailure = false;
  }

  /**
   * @return newly created simple quantified formula.
   */
  private static AbstractFormula sampleQuantifiedFormula() {
    final QuantifiedFormula f = new QuantifiedFormula(Code.FORALL_WITH_NAME);
    final BoundVar bv = new BoundVar(JavaBasicType.JavaInt, 0, f, "a");
    f.addVariable(bv);
    f.setFormula(new Predicate2Ar(Code.LESS, bv, new NumberLiteral(10)));
    return f;
  }

  /**
   * Single test scenario for {@link CodeFragment} class.
   * Replaces given fragment of bytecode with sth incorrect
   * and gives it to {@link CodeFragment} class to parse it.
   * Notifies if it's behavior changes.
   *
   * @param from - beginning of replaced fragment,
   * @param to - end of replaced fragment,
   * @param hash - model state ({@link CodeFragment#hash()}
   *     method result) of {@link CodeFragment} class
   *     after parsing given sample.
   * @see #singleTest(String, String, int, String, int)
   */
  private static void singleTest(final String from, final String to,
                                 final int hash) {
    final int cfrom = code.indexOf(from) + from.length();
    final int cto = code.indexOf(to, cfrom);
    String newCode = "XXX" + code.substring(cfrom, cto);
    newCode = newCode.toUpperCase(); // changes sth.
    singleTest(from, to, hash, newCode, 0);
  }

  /**
   * Single test scenario for {@link CodeFragment} class.
   * Replaces given fragment of bytecode with given String.
   * and gives it to {@link CodeFragment} class to parse it.
   * Notifies if it's behavior changes (if it has diffrent
   * {@link CodeFragment#hash()} value).
   * Replaced fragment is first fragment starting just after
   * first occurence of <code>from</code> text, and ending
   * just befor first following occurence
   * of <code>to</code> text.
   *
   * @param from - beginning of replaced fragment,
   * @param to - end of replaced fragment,
   * @param hash - model state ({@link CodeFragment#hash()}
   *     method result) of {@link CodeFragment} class
   *     after parsing given sample.
   * @param newCode - code fragment to replace given
   *    fragment.
   * @param correct - whether this sample is correct or not.
   * @return true if {@link CodeFragment}'s reaction for
   *     this sample was as expected (in <code>hash</code>
   *     and <code>correct</code> parameters).
   */
  private static boolean singleTest(final String from, final String to,
                                    final int hash, final String newCode,
                                    final int correct) {
    System.out.println("************ test nr " + test_nr + " ************");
    boolean ret = true;
    if (correct  <  -1 || correct  >  1) {
      throw new RuntimeException("invalid parameter value.");
    }
    final int oldMask = MLog.getLogMask();
    if (!goDisplayAllMessages) {
      MLog.setLogMask(MLog.MASK_PERRORS);
    }
    CodeFragment cf = new CodeFragment(bcc, code);
    final int cfrom = code.indexOf(from) + from.length();
    int cto = code.length() - 1;
    if (to != null) {
      cto = code.indexOf(to, cfrom);
    }
    //cf.addChange(cfrom, cto - cfrom, newCode);
    cf.performChanges();
    if (correct != 0) {
      boolean ok = cf.isCorrect();
      if (correct == 1 && !ok) {
        ret = false;
        cf = new CodeFragment(bcc, code);
        MLog.setLogMask(oldMask);
        cf.modify(cfrom, cto - cfrom, newCode);
        System.out.println("Test " + test_nr + ": code replace failed!");
      }
      if (correct == -1 && ok) {
        ret = false;
        MLog.setLogMask(oldMask);
        cf = new CodeFragment(bcc, code);
        cf.modify(cfrom, cto - cfrom, newCode);
        System.out.println("Test " + test_nr + ": syntax error not detected!");
      }
    }
//    final int h = cf.hash();
//    System.out.print("hash = " + h);
//    if (h == hash) {
//      System.out.println(" (ok)");
//    } else {
//      if (hash == -1) {
//        System.out.println(" (not set yet)");
//      } else {
//        ret = false;
//        System.out.println(" (should be " + hash + ")");
//      }
//      MLog.setLogMask(oldMask);
//      cf = new CodeFragment(bcc, code);
//      cf.modify(cfrom, cto - cfrom, newCode);
//    }
    MLog.setLogMask(oldMask);
    test_nr++;
    if (!ret) {
      errc++;
    }
    return ret;
  }

  /**
   * A simple test for searching for fields
   * and localVariables by name.
   */
  private static void variableSearchTest() throws ClassNotFoundException,
      ReadAttributeException {
    final String fname = "text";
    bcc = createSampleClass();
    System.out.println(bcc.printCode());
    System.out.println(xxx);
    final int fi = bcc.getFieldIndex(fname);
    System.out.println(bcc.getCp().getConstant(fi).toString());
    final String vname = "last";
    final FieldRef fr = new FieldRef(false, bcc.getCp(), fi);
    System.out.println("field name, should be '" + fname + "': "
                       + fr.toString());
    final LocalVariable lv = bcc.getMethod(2)
        .findLocalVariable(vname, bcc.getMethod(2).findAtPC(19));
    System.out.println("start_pc = "
                       + lv.getBcelLvGen().getStart().getPosition());
    System.out.println("local variable name, should be '" + vname + "': "
                       + lv.getName());
  }

}

/**
 * Simple class for storeing an integer value.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 */
class myInt {
  public int value = 0;
}
