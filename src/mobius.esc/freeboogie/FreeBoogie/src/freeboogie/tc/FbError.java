package freeboogie.tc;

import java.util.List;

import freeboogie.ast.Ast;
import genericutils.Err;

/**
 * Represents an error.
 *
 * Various analyzes of the AST produce lists of errors. Each
 * error has a type, points to an AST node, and contains
 * additional information used to build up an error message
 * when {@code toString()} is called.
 *
 * @author rgrig
 */
public class FbError {
  /** Types of errors. */
  public static enum Type {
    UNDECL_ID("Undeclared identifier %."),
    REQ_SPECIALIZATION("Explicit specialization required for %0 at %1."),
    GEN_TOOMANY("Too many explicit generics."),
    NOT_SUBTYPE("Found type %0 instead of %1."),
    BAD_TYPE("Unrelated types: %0 and %1."),
    EXACT_TYPE("Type should be %."),
    TV_ALREADY_DEF("Type variable % already defined."),
    ALREADY_DEF("Variable % already defined"),
    GB_ALREADY_DEF("Identifier % was already defined."),
    MISSING_BLOCK("Inexistent block %."),
    IP_CNT_MISMATCH("Implementation-Procedure parameter count mismatch."),
    DEP_IMPL_SIG("Dependent type in implementation signature."),
    PROC_MISSING("Implementation without procedure."),
    NEED_ARRAY("Must be a map.");

    private final String templ;
    public String templ() { return templ; }
    Type(String templ) { this.templ = templ; }
  }

  private final Type type;
  private final Ast ast;
  private final Object[] data;

  /**
   * Constructs an error of type {@code type} that refers to
   * the ast node {@code ast} and carries the additional data
   * {@code data}. Note that the content of {@code data} is
   * not checked.
   */
  public FbError(Type type, Ast ast, Object... data) {
    assert type != null;
    assert ast != null;
    this.type = type;
    this.ast = ast;
    this.data = data;
  }

  /** Returns the type of this error. */
  public Type type() { return type; }

  /** Returns the primary AST node associated with this error. */
  public Ast place() { return ast; }

  /** Allows users to explicitely read the attached data. */
  public Object data(int idx) { return data[idx]; }

  /**
   * Constructs a message from the template and the data.
   * The template can contain "%3" to print the fourth data.
   * You can use "%%" to print "%". A single "%" not followed
   * by a number is equivalent to "%0".
   *
   * It may fail with a out-of-bounds exception if not enough
   * data was provided when the error was created.
   */
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(ast.loc());
    sb.append(": ");
    int n = type.templ().length();
    for (int i = 0; i < n; ++i) {
      char c = type.templ().charAt(i);
      if (c != '%') sb.append(c);
      else if (i+1 < n && type.templ().charAt(i+1) == '%') {
        ++i; sb.append('%');
      } else {
        int idx = 0;
        while (i+1 < n && Character.isDigit(c = type.templ().charAt(i+1))) {
          idx = 10 * idx + c - '0';
          ++i;
        }
        try {
          sb.append(data[idx].toString());
        } catch (Exception e) {
          Err.error(e.toString());
          Err.internal("INTERNAL ERROR: idx="+idx + " err_type="+type);
        }
      }
    }
    return sb.toString();
  }

  public static boolean reportAll(List<FbError> es) {
    for (FbError e : es) Err.error(e.toString());
    return !es.isEmpty();
  }
}
