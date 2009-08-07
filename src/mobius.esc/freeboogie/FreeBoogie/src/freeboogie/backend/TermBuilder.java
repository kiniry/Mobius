package freeboogie.backend;

import java.math.BigInteger;
import java.util.ArrayList;

import genericutils.Err;
import genericutils.Logger;
import genericutils.StackedHashMap;

import freeboogie.ast.Expr;
import freeboogie.tc.TcInterface;

import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;

/**
 * This class is responsible for sort-checking. The subclasses
 * are responsible for actually building a data structure (or calling
 * the prover to construct such a data structure inside it).
 *
 * Terms can be built by specifying a name and arguments, or by
 * giving a BoogiePL expression to be converted into a Term.
 *
 * @param <T> the type of terms
 *
 * @author rgrig 
 */
public abstract class TermBuilder<T extends Term<T>> {
  private Logger<LogCategories, LogLevel> log =
    Logger.<LogCategories, LogLevel>get("log");

  protected FormulaOfExpr<T> term;

  private StackedHashMap<String, TermDef> termDefs =
    new StackedHashMap<String, TermDef>();

  public TermBuilder() {
    // Register terms that are necessary to translate Boogie
    // expressions Classes that implement Prover should know how
    // to communicate these to the provers they wrap.
    def("not", new Sort[]{Sort.FORMULA}, Sort.FORMULA);
    def("and", Sort.FORMULA, Sort.FORMULA);
    def("or", Sort.FORMULA, Sort.FORMULA);
    def("iff", new Sort[]{Sort.FORMULA, Sort.FORMULA}, Sort.FORMULA);
    def("implies", new Sort[]{Sort.FORMULA, Sort.FORMULA}, Sort.FORMULA);

    def("var", String.class, Sort.VARTERM);
    def("var_int", String.class, Sort.VARINT);
    def("var_bool", String.class, Sort.VARBOOL);
    def("var_formula", String.class, Sort.VARFORMULA);

    def("literal", String.class, Sort.TERM);
    def("literal_int", BigInteger.class, Sort.INT);
    def("literal_bool", Boolean.class, Sort.BOOL);
    def("literal_formula", Boolean.class, Sort.FORMULA);

    def("forall", new Sort[]{Sort.VARTERM, Sort.FORMULA}, Sort.FORMULA);
    def("forall_int", new Sort[]{Sort.VARINT, Sort.FORMULA}, Sort.FORMULA);
    def("forall_bool", new Sort[]{Sort.VARBOOL, Sort.FORMULA}, Sort.FORMULA);
    def("exists", new Sort[]{Sort.VARTERM, Sort.FORMULA}, Sort.FORMULA);
    def("exists_int", new Sort[]{Sort.VARINT, Sort.FORMULA}, Sort.FORMULA);
    def("exists_bool", new Sort[]{Sort.VARBOOL, Sort.FORMULA}, Sort.FORMULA);

    def("+", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("-", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("*", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("/", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("%", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("<", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def("<=", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def(">=", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def(">", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);

    def("eq", new Sort[]{Sort.TERM, Sort.TERM}, Sort.FORMULA);
    def("eq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def("eq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.FORMULA);
    def("neq", new Sort[]{Sort.TERM, Sort.TERM}, Sort.FORMULA);
    def("neq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def("neq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.FORMULA);

    def("tuple", Sort.TERM, Sort.TERM);
    def("map_select", new Sort[]{Sort.TERM, Sort.TERM}, Sort.TERM);
    def("map_select_int", new Sort[]{Sort.TERM, Sort.TERM}, Sort.INT);
    def("map_select_bool", new Sort[]{Sort.TERM, Sort.TERM}, Sort.BOOL);
    def("map_update", new Sort[]{Sort.TERM, Sort.TERM, Sort.TERM}, Sort.TERM);

    def("<:", new Sort[]{Sort.TERM, Sort.TERM}, Sort.BOOL);
    def("distinct", Sort.TERM, Sort.FORMULA);

    // handles casts, doesn't get printed; shouldn't be in Boogie
    def("cast_to_int", new Sort[]{Sort.TERM}, Sort.INT);
    def("cast_to_bool", new Sort[]{Sort.TERM}, Sort.BOOL);

    // These are used to mimic formulas in terms. Each has an
    // axiom associated.
    def("Tnand", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.BOOL);
    def("T<", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);
    def("Teq", new Sort[]{Sort.TERM, Sort.TERM}, Sort.BOOL);
    def("Teq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);
    def("Teq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.BOOL);

    def("Tforall", new Sort[]{Sort.VARTERM, Sort.BOOL}, Sort.BOOL);
    def("Tforall_int", new Sort[]{Sort.VARINT, Sort.BOOL}, Sort.BOOL);
    def("Tforall_bool", new Sort[]{Sort.VARBOOL, Sort.BOOL}, Sort.BOOL);
    def("Texists", new Sort[]{Sort.VARTERM, Sort.BOOL}, Sort.BOOL);
    def("Texists_int", new Sort[]{Sort.VARINT, Sort.BOOL}, Sort.BOOL);
    def("Texists_bool", new Sort[]{Sort.VARBOOL, Sort.BOOL}, Sort.BOOL);


    pushDef(); // mark the end of the prover builtin definitions

    term = new FormulaOfExpr<T>(new TermOfExpr<T>());
    term.setBuilder(this);
    log.say(LogCategories.BACKEND, LogLevel.INFO, "TermBuilder ready.");
  }
  
  /** 
   * Sets the type checker used to figure out the sorts when
   * translating Boogie expressions.
   */
  public void setTypeChecker(TcInterface tc) { term.setTypeChecker(tc); }

  /** Constructs a term out of a Boogie expression. */
  public T of(Expr e) { return e.eval(term); }
 
  /**
   * Define {@code name : s1 x ... x sn -> s}.
   * @param name a unique identifier
   * @param argSorts {@code s1 x ... x sn}
   * @param retSort {@code s}
   */
  public void def(String name, Sort[] argSorts, Sort retSort) {
    termDefs.put(name, new TermDef(argSorts, retSort));
  }

  /**
   * Define {@code name : [sa] -> sr}.
   * @param name a unique identifier
   * @param naryArgSort {@code sa}
   * @param retSort {@code sr}
   */
  public void def(String name, Sort naryArgSort, Sort retSort) {
    termDefs.put(name, new TermDef(naryArgSort, retSort));
  }

  /**
   * This maps a Java type to a prover sort.
   * @param name a unique identifier (for example, "literal_int")
   * @param cls the Java type
   * @param retSort the prover sort
   */
  public void def(String name, Class cls, Sort retSort) {
    termDefs.put(name, new TermDef(cls, retSort));
  }
  
  /**
   * Undefines a term.
   * @param name the unique identifier of the term
   */
  public void undef(String name) {
    termDefs.remove(name);
  }
  
  /**
   * Start a new `definitions frame'.
   */
  public void pushDef() {
    termDefs.push();
  }

  /**
   * Discard the last `definitions frame'.
   */
  public void popDef() {
    termDefs.pop();
  }
  
  /**
   * Retrieve a previously defined term.
   * @param name a unique id
   * @return the prover sort of {@code name}
   */
  public TermDef getTermDef(String name) {
    return termDefs.get(name);
  }
  
  /**
   * Constructs a prover constant from the Java object {@code a}.
   * @param termId the term definition that allows this mapping
   * @param a the argument
   * @return the constructed term
   */
  public final T mk(String termId, Object a) {
//System.out.println("mk1> " + termId);
    TermDef def = getTermDef(termId);
    if (def == null) 
      Err.internal("sort " + termId + " not registered");
    if (def.cls == null)
      Err.internal("sort " + termId + " has no Java type associated");
    if (!def.cls.isInstance(a)) {
      Err.internal("trying to build " + termId + " using " + a
        + " instead of something of type " + def.cls.getCanonicalName());
    }
    return reallyMk(def.retSort, termId, a);
  }

  /** Helper for unary operators. */
  public final T mk(String termId, T a) {
    ArrayList<T> all = new ArrayList<T>(3);
    all.add(a);
    return mk(termId, all);
  }

  /** Helper for binary operators. */
  public final T mk(String termId, T a, T b) {
    ArrayList<T> all = new ArrayList<T>(7);
    all.add(a);
    all.add(b);
    return mk(termId, all);
  }
  
  /**
   * Constructs a term with of the identified by {@code termId}
   * that takes {@code a} as arguments.
   * 
   * @param termId identifies the term to be built
   * @param a the arguments
   * @return the newly built term
   */
  public final T mk(String termId, ArrayList<T> a) {
    TermDef def = getTermDef(termId);
    if (def == null) Err.internal("Unregistered sort " + termId);
    for (T t : a) assert t != null;
    if (def.naryArgSort != null) {
      for (T t : a) {
        if (!t.sort().isSubsortOf(def.naryArgSort)) {
          Err.internal(
            "" + t + ":" + t.sort() + " is used as an argument of '"
            + termId + "' where sort " + def.naryArgSort + " is expected.");
        }
      }
      return reallyMkNary(def.retSort, termId, a);
    } else {
      assert def.argSorts.length == a.size();
      for (int i = 0; i < a.size(); ++i) {
        if (!a.get(i).sort().isSubsortOf(def.argSorts[i])) {
          Err.internal(
            "" + a.get(i) + ":" + a.get(i).sort() + " is used as an argument of '"
            + termId + "' where sort " + def.argSorts[i] + " is expected.");
        }
      }
      return reallyMk(def.retSort, termId, a);
    }
  }

  /**
   * Subclasses should either construct a tree ar communicate with
   * the prover such that the prover constructs a tree.
   * 
   * @param termId the term to be constructed
   * @param a the argument
   * @return the constructed term
   */
  protected abstract T reallyMk(Sort sort, String termId, Object a);
  
  /**
   * Subclasses should either construct a tree ar communicate with
   * the prover such that the prover constructs a tree.
   * 
   * @param termId the term to be constructed
   * @param a the arguments
   * @return the constructed term
   */
  protected abstract T reallyMk(Sort sort, String termId, ArrayList<T> a);
  
  /**
   * Subclasses should either construct a tree ar communicate with
   * the prover such that the prover constructs a tree.
   * 
   * @param termId the term to be constructed
   * @param a the arguments
   * @return the constructed term
   */
  protected abstract T reallyMkNary(Sort sort, String termId, ArrayList<T> a);
}
