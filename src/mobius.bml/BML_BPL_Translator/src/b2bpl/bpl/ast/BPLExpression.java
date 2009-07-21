package b2bpl.bpl.ast;


public abstract class BPLExpression extends BPLNode {

  public static final BPLExpression[] EMPTY_ARRAY = new BPLExpression[0];

  protected final Precedence precedence;

  private BPLType type;

  protected BPLExpression(Precedence precedence) {
    this.precedence = precedence;
  }

  public final Precedence getPrecedence() {
    return precedence;
  }

  public boolean isPredicate() {
    return false;
  }

  public final BPLType getType() {
    return type;
  }

  public final void setType(BPLType type) {
    this.type = type;
  }

  public static enum Precedence {

    EQUIVALENCE(0),

    IMPLICATION(1),

    AND_OR(2),

    EQUALITY(3),

    // REVIEW[om]: Currently, Boogie gives equality and relational operators the
    //             same precedence. This seems to be a bug but we have to adhere
    //             to it since, otherwise, we would wrongly parenthesize
    //             expressions in some cases. Note that as long as this
    //             precedence is only used for generating parentheses in a
    //             pretty printer, there is no issue in having this wrong
    //             precedence. Nevertheless, the precedence should be corrected
    //             as soon as Boogie behaves as expected.
    RELATIONAL(3),

    ADDITIVE(5),

    MULTIPLICATIVE(6),

    UNARY(7),

    ATOM(8),

    LOWEST(EQUIVALENCE.value),

    HIGHEST(ATOM.value);

    private final int value;

    private Precedence(int value) {
      this.value = value;
    }

    public int compare(Precedence other) {
      return value - other.value;
    }
  }
}
