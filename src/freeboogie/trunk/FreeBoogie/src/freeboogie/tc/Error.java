package freeboogie.tc;

import freeboogie.ast.Ast;

public class Error {
  static public enum Type {
    // TODO: Find better names for these errors
    UNDECL_ID("Undeclared identifier %."),
    REQ_SPECIALIZATION("Explicit specialization required for %0 at %1."),
    GEN_TOOMANY("Too many explicit generics. Ignoring."),
    NOT_SUBTYPE("Found type %0 instead of %1."),
    BAD_TYPE("Unrelated types: %0 and %1."),
    EXACT_TYPE("Type should be %."),
    TV_ALREADY_DEF("Type variable % already defined."),
    ALREADY_DEF("Variable % already defined"),
    GB_ALREADY_DEF("Identifier % already defined."),
    MISSING_BLOCK("Inexistent block %."),
    IP_CNT_MISMATCH("Implementation-Procedure parameters count mismatch."),
    DEP_IMPL_SIG("Dependent type in implementation signature."),
    PROC_MISSING("Implementation without procedure.");

    private final String templ;
    public String templ() { return templ; }
    Type(String templ) { this.templ = templ; }
  }

  private Type type;
  private Ast ast;
  private Object[] data;

  /**
   * Constructs an error of type {@code type} that refers to
   * the ast node {@code ast} and carries the additional data
   * {@code data}. Note that the content of {@code data} is
   * not checked.
   */
  public Error(Type type, Ast ast, Object... data) {
    assert ast != null;
    this.ast = ast;
    this.data = data;
  }

  /**
   * Constructs a message from the template and the data.
   * The template can contain "%3" to print the fourth data.
   * You can use "%%" to print "%". A single "%" not followed
   * by a number is equivalent to "%0".
   *
   * It may fail with a out-of-bounds exception if not enough
   * data was provided when the error was created.
   *
   * TODO: Test this.
   */
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(ast.loc());
    sb.append(": ");
    int n = type.templ.length();
    for (int i = 0; i < n; ++i) {
      char c = type.templ().charAt(i);
      if (c != '%') sb.append(c);
      else if (i+1 < n && type.templ().charAt(i+1) == '%') {
        ++i; sb.append('%');
      } else {
        int idx = 0;
        while (i+1 < n && Character.isDigit(c = type.templ().charAt(i+1)))
          idx = 10 * idx + c - '0';
        sb.append(data[idx].toString());
      }
    }
    return sb.toString();
  }
}
