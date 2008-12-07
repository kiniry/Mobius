package freeboogie.backend;

import java.util.logging.Logger;

import freeboogie.ast.Expr;
import freeboogie.tc.TcInterface;
import freeboogie.util.Err;
import freeboogie.util.StackedHashMap;

/**
 * This class is responsible for sort-checking. The subclasses
 * are responsible for actually building a data structure (or calling
 * the prover to construct such a data structure inside it).
 *
 * Terms can be built by specifying a name and arguments, or by
 * giving a BoogiePL expression to be converted into a Term.
 *
 * @author rgrig 
 */
public abstract class TermBuilder {
  private static Logger log = Logger.getLogger("freeboogie.backend");

  protected FormulaOfExpr term;

  private StackedHashMap<String, TermDef> termDefs =
    new StackedHashMap<String, TermDef>();

  public TermBuilder() {
    term = new FormulaOfExpr(new TermOfExpr());
    term.setBuilder(this);
  }
  
  /** 
   * Sets the type checker used to figure out the sorts when
   * translating Boogie expressions.
   */
  public void setTypeChecker(TcInterface tc) { term.setTypeChecker(tc); }

  /** Constructs a term out of a Boogie expression. */
  public Term of(Expr e) { return (SmtTerm)e.eval(term); }
 
  /**
   * Define {@code name : s1 x ... x sn -> s}.
   * @param name a unique identifier
   * @param argSorts {@code s1 x ... x sn}
   * @param retSort {@code s}
   */
  public void def(String name, Sort[] argSorts, Sort retSort) {
    log.fine("register symbol " + name);
    termDefs.put(name, new TermDef(argSorts, retSort));
  }

  /**
   * Define {@code name : [sa] -> sr}.
   * @param name a unique identifier
   * @param naryArgSort {@code sa}
   * @param retSort {@code sr}
   */
  public void def(String name, Sort naryArgSort, Sort retSort) {
    log.fine("register nary symbol " + name);
    termDefs.put(name, new TermDef(naryArgSort, retSort));
  }

  /**
   * This maps a Java type to a prover sort.
   * @param name a unique identifier (for example, "const_int")
   * @param cls the Java type
   * @param retSort the prover sort
   */
  public void def(String name, Class cls, Sort retSort) {
    log.fine("register meta-symbol " + name + " for Java type " + cls.getName());
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
  public final Term mk(String termId, Object a) {
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
  
  /**
   * Helper for constructing terms with only one argument.
   * @param termId what term to be constructed
   * @param a the argument
   * @return the constructed term
   */
  public final Term mk(String termId, Term a) {
    return mk(termId, new Term[] {a});
  }
  
  /**
   * Helper for constructing terms with only two arguments.
   * 
   * @param termId what term to construct
   * @param a the first argument
   * @param b the second argument
   * @return the newly constructed term
   */
  public final Term mk(String termId, Term a, Term b) {
    return mk(termId, new Term[] {a, b});
  }
  
  /**
   * Constructs a term with of the identified by {@code termId}
   * that takes {@code a} as arguments.
   * 
   * @param termId identifies the term to be built
   * @param a the arguments
   * @return the newly built term
   */
  public final Term mk(String termId, Term[] a) {
    TermDef def = getTermDef(termId);
    if (def == null) Err.internal("Unregistered sort " + termId);
    for (int i = 0; i < a.length; ++i)
      assert a[i] != null; // hmm
    if (def.naryArgSort != null) {
      for (int i = 0; i < a.length; ++i) {
        if (!a[i].sort().isSubsortOf(def.naryArgSort)) {
          Err.internal(
            "" + a[i] + ":" + a[i].sort() + " is used as an argument of '"
            + termId + "' where sort " + def.naryArgSort + " is expected.");
        }
      }
      return reallyMkNary(def.retSort, termId, a);
    } else {
      assert def.argSorts.length == a.length;
      for (int i = 0; i < a.length; ++i) {
        if (!a[i].sort().isSubsortOf(def.argSorts[i])) {
          Err.internal(
            "" + a[i] + ":" + a[i].sort() + " is used as an argument of '"
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
  protected abstract Term reallyMk(Sort sort, String termId, Object a);
  
  /**
   * Subclasses should either construct a tree ar communicate with
   * the prover such that the prover constructs a tree.
   * 
   * @param termId the term to be constructed
   * @param a the arguments
   * @return the constructed term
   */
  protected abstract Term reallyMk(Sort sort, String termId, Term[] a);
  
  /**
   * Subclasses should either construct a tree ar communicate with
   * the prover such that the prover constructs a tree.
   * 
   * @param termId the term to be constructed
   * @param a the arguments
   * @return the constructed term
   */
  protected abstract Term reallyMkNary(Sort sort, String termId, Term[] a);
}
