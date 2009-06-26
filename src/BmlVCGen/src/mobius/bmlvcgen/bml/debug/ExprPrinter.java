package mobius.bmlvcgen.bml.debug;

import java.util.ArrayList;
import java.util.List;

import mobius.bmlvcgen.bml.ExprVisitor;
import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.bml.debug.Operator.Assoc;
import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.bml.types.TypePrinter;
import mobius.bmlvcgen.util.Visitable;

/**
 * Base class of objects used to convert
 * BML expressions to strings.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Subclass type.
 */
public abstract class 
ExprPrinter<V> implements ExprVisitor<V> {
  
  /**
   * Operators used by this visitor.
   */
  private enum Op implements Operator {
      ID("", Integer.MAX_VALUE, Assoc.NOASSOC),
      DOT(".", 1200, Assoc.NOASSOC), 
      FORALL("\\forall", 1101, Assoc.NOASSOC),
      EXISTS("\\forall", 1101, Assoc.NOASSOC),
      UMINUS("-", 1100, Assoc.NOASSOC),
      NOT("!", 1100, Assoc.NOASSOC),
      BITNEG("~", 1100, Assoc.NOASSOC),
      MUL("*", 1000, Assoc.LEFT), 
      DIV("/", 1000, Assoc.LEFT), 
      MOD("%", 1000, Assoc.LEFT),
      PLUS("+", 800, Assoc.LEFT),
      MINUS("-", 800, Assoc.LEFT),
      SHL("<<", 700, Assoc.LEFT),
      SHR(">>>", 700, Assoc.LEFT),
      SAR(">>", 700, Assoc.LEFT),
      LT("<", 500, Assoc.LEFT),
      LE("<=", 500, Assoc.LEFT),
      GT(">", 500, Assoc.LEFT),
      GE(">=", 500, Assoc.LEFT),
      SUBTYPE("<:", 500, Assoc.LEFT),
      EQ("==", 450, Assoc.LEFT),
      NEQ("!=", 450, Assoc.LEFT),
      BITAND("&", 400, Assoc.LEFT),
      BITXOR("^", 350, Assoc.LEFT),
      BITOR("|", 300, Assoc.LEFT),
      AND("&&", 250, Assoc.LEFT),
      OR("||", 200, Assoc.LEFT),
      IMPL("==>", 150, Assoc.LEFT),
      RIMPL("<==", 150, Assoc.RIGHT),
      EQUIV("<==>", 100, Assoc.NOASSOC),
      INEQUIV("<=!=>", 100, Assoc.NOASSOC),
      ROOT(":-(", Integer.MIN_VALUE, Assoc.NOASSOC);

    private final String text;
    private final int priority;
    private final Assoc assoc;
    
    private Op(final String text, 
               final int priority, 
               final Assoc assoc) {
      this.text = text;
      this.priority = priority;
      this.assoc = assoc;
    }

    /** {@inheritDoc} */
    public Assoc getAssoc() {
      return assoc;
    }

    /** {@inheritDoc} */
    public int getPriority() {
      return priority;
    }

    /** {@inheritDoc} */
    public String getText() {
      return text;
    }
    
  }
  
  // Builder used to construct the expression.
  private final StringBuilder builder;
  
  // Parent operator (when processing subexpressions recursively).
  private Operator parentOp = Op.ROOT;
  
  // Are we processing left subexpression?
  private boolean left;
  
  // Quantifier stack - remembers names of
  // quantified variables. For unnamed variables
  // entries of the form vN are stored.
  private final List<String> quantifierStack;
  
  // Counter for unnamed bound variables.
  private int vcount;
  
  /**
   * Constructor.
   */
  protected ExprPrinter() {
    builder = new StringBuilder();
    quantifierStack = new ArrayList<String>();
  }
  
  /**
   * This method should be called before
   * a new expression is passed to this
   * visitor.
   */
  public void clear() {
    builder.delete(0, builder.length());
  }
  
  /**
   * Get string representation of last expression
   * visited by this visitor,
   * @return Text.
   */
  public String getText() {
    return builder.toString();
  }

  /**
   * Return this pointer.
   * @return This pointer.
   */
  protected abstract V getThis();
  
  /**
   * Append text to builder.
   * Used by subclasses.
   * @param text Text to append.
   */
  protected void append(final String text) {
    builder.append(text);
  }
  
  /**
   * Visit binary expression.
   * @param l Left operand.
   * @param r Right operand.
   * @param op Operator.
   * @param <Expr> Type of expressions.
   */
  protected <Expr extends Visitable<? super V>>
  void visitBinary(final Expr l, final Expr r, 
                             final Operator op) {
    final Operator p = getParentOp();
    final boolean parens = needParens(op, p, isLeft());
    
    setParentOp(op);
    if (parens) {
      append("(");
    }
    setLeft(true);
    l.accept(getThis());
    append(" ");
    append(op.getText());
    append(" ");
    setLeft(false);   // setRight() ?
    r.accept(getThis());
    if (parens) {
      append(")");
    }
    setParentOp(p);
  }

  /**
   * Visit unary expression.
   * @param arg Argument
   * @param op Operator.
   * @param <Expr> Type of expressions.
   */
  protected <Expr extends Visitable<? super V>>
  void visitUnary(final Expr arg, final Operator op) {
    final Operator p = getParentOp();
    final boolean parens = needParens(op, p, isLeft());
    setParentOp(op);
    if (parens) {
      append("(");
    }
    arg.accept(getThis());
    if (parens) {
      append(")");
    }
    setParentOp(p);
  }
  
  // Are parentheses needed around this expression?
  // @param op Operator.
  // @param p Parent operator.
  // @param lft True if processing left subexpression.
  private boolean needParens(final Operator op,
                             final Operator pop,
                             final boolean lft) {
    final int p1 = op.getPriority();
    final int p2 = pop.getPriority();
    if (lft) {
      return (p1 < p2 || (p1 == p2 && 
          (pop.getAssoc() != Assoc.LEFT && 
              pop.getAssoc() != Assoc.BOTH)));
    } else {
      return (p1 < p2 || (p1 == p2 && 
          (pop.getAssoc() != Assoc.RIGHT && 
              pop.getAssoc() != Assoc.BOTH)));
    }
  }
  
  /**
   * Get parent operator.
   * @return Parent operator.
   */
  protected final Operator getParentOp() {
    return parentOp;
  }

  /**
   * Are we visiting left subexpression?
   * @return True if visiting left subexpression.
   */
  protected final boolean isLeft() {
    return left;
  }

  /**
   * Set 'left' value. 
   * @param left True for left subexpression, false for right.
   */
  protected final void setLeft(final boolean left) {
    this.left = left;
  }

  /**
   * Set parent operator.
   * @param parentOp Parent operator.
   */
  protected final void setParentOp(final Operator parentOp) {
    this.parentOp = parentOp;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void arrayAccess(final Expr array, final Expr index) {
    array.accept(getThis());
    append("[");
    index.accept(getThis());
    append("]");
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void arrayLength(final Expr array) {
    final Operator pop = getParentOp();
    setParentOp(Op.DOT);
    array.accept(getThis());
    append(".length");
    setParentOp(pop);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void call(final Expr obj, 
            final MethodName method, 
            final Expr... args) {
    final MethodNamePrinter mn = 
      new MethodNamePrinter();
    obj.accept(getThis());
    method.accept(mn);
    append(".");
    append(mn.getName());
    append("(");
    for (int i = 0; i < args.length; i++) {
      args[i].accept(getThis());
      if (i + 1 < args.length) {
        append(", ");
      }
    }
    append(")");
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void cond(final Expr cnd, 
            final Expr ifTrue, 
            final Expr ifFalse) {
    append("(");
    cnd.accept(getThis());
    append(" ? ");
    ifTrue.accept(getThis());
    append(" : ");
    ifFalse.accept(getThis());
    append(")");
  }
  
  /** {@inheritDoc} */
  public void constNull() {
    append("null");
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void getField(final Expr obj, 
                       final String field,
                       final Type type) {
    final Operator pop = getParentOp();
    setParentOp(Op.DOT);
    obj.accept(getThis());
    append(".");
    append("field");
    setParentOp(pop);    
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void getField(final String field, final Type type) {
    append(field);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void self() {
    append("this");
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolAnd(final Expr l, final Expr r) {
    visitBinary(l, r, Op.AND);
  }
  
  /** {@inheritDoc} */
  public void boolConst(final boolean v) {
    append(Boolean.toString(v));
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolEquiv(final Expr l, final Expr r) {
    visitBinary(l, r, Op.EQUIV);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolImpl(final Expr l, final Expr r) {
    visitBinary(l, r, Op.IMPL);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolInequiv(final Expr l, final Expr r) {
    visitBinary(l, r, Op.INEQUIV);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolNot(final Expr e) {
    visitUnary(e, Op.NOT);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolOr(final Expr l, final Expr r) {
    visitBinary(l, r, Op.OR);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void boolRimpl(final Expr l, final Expr r) {
    visitBinary(l, r, Op.RIMPL);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void eq(final Expr l, final Expr r) {
    visitBinary(l, r, Op.EQ);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void ge(final Expr l, final Expr r) {
    visitBinary(l, r, Op.GE);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void gt(final Expr l, final Expr r) {
    visitBinary(l, r, Op.GT);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void isSubtype(final Expr l, final Expr r) {
    visitBinary(l, r, Op.SUBTYPE);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void le(final Expr l, final Expr r) {
    visitBinary(l, r, Op.LE);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void lt(final Expr l, final Expr r) {
    visitBinary(l, r, Op.LT);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void neq(final Expr l, final Expr r) {
    visitBinary(l, r, Op.NEQ);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void add(final Expr l, final Expr r) {
    visitBinary(l, r, Op.PLUS);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void bitAnd(final Expr l, final Expr r) {
    visitBinary(l, r, Op.BITAND);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void bitNeg(final Expr e) {
    visitUnary(e, Op.BITNEG);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void bitOr(final Expr l, final Expr r) {
    visitBinary(l, r, Op.BITOR);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void bitXor(final Expr l, final Expr r) {
    visitBinary(l, r, Op.BITXOR);
  }

  /** {@inheritDoc} */
  public void byteConst(final byte v) {
    append(Byte.toString(v));
  }

  /** {@inheritDoc} */
  public void charConst(final char v) {
    append("'");
    append(String.valueOf(v));
    append("'");
  }

  /** {@inheritDoc} */
  public void intConst(final int v) {
    append(String.valueOf(v));
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void intDiv(final Expr l, final Expr r) {
    visitBinary(l, r, Op.DIV);
  }

  /** {@inheritDoc} */
  public void longConst(final long v) {
    append(String.valueOf(v));
    append("L");
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void minus(final Expr e) {
    visitUnary(e, Op.UMINUS);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void mod(final Expr l, final Expr r) {
    visitBinary(l, r, Op.MOD);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void mul(final Expr l, final Expr r) {
    visitBinary(l, r, Op.MUL);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void sar(final Expr l, final Expr r) {
    visitBinary(l, r, Op.SAR);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void shl(final Expr l, final Expr r) {
    visitBinary(l, r, Op.SHL);
  }

  /** {@inheritDoc} */
  public void shortConst(final short v) {
    append(String.valueOf(v));
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void shr(final Expr l, final Expr r) {
    visitBinary(l, r, Op.SHR);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void sub(final Expr l, final Expr r) {
    visitBinary(l, r, Op.MINUS);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void cast(final Type t, final Expr e) {
    final TypePrinter tp = new TypePrinter();
    t.accept(tp);
    final Operator pop = getParentOp();
    setParentOp(Op.ROOT);
    append("(");
    append("(");
    append(tp.getExternalName());
    append(")");
    e.accept(getThis());
    append(")");
    setParentOp(pop);
  }

  /** {@inheritDoc} */
  public void typeConst(final Type t) {
    final TypePrinter tp = new TypePrinter();
    t.accept(tp);
    append(tp.getExternalName());
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void exists(final Expr expr, 
                     final String varName, 
                     final Type type) {
    final String name;
    if (varName == null) {
      name = "v" + vcount++;
    } else {
      name = varName;
    }
    quantifierStack.add(0, name);
    visitUnary(expr, Op.EXISTS);
    quantifierStack.remove(0);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void forall(final Expr expr, 
                     final String varName,
                     final Type type) {
    final String name;
    if (varName == null) {
      name = "v" + vcount++;
    } else {
      name = varName;
    }
    quantifierStack.add(0, name);
    visitUnary(expr, Op.FORALL);
    quantifierStack.remove(0);    
  }
  
  
  /** {@inheritDoc} */
  public void boundvar(final int level) {
    if (level >= 0 && level < quantifierStack.size()) {
      append(quantifierStack.get(level));
    } else {
      append("<ERROR-BOUND-VAR>");
    }
  }
  
}
