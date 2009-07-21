package mobius.bmlvcgen.vcgen;

import java.util.ArrayList;
import java.util.List;

import mobius.bmlvcgen.bml.ExprVisitor;
import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.util.Visitable;
import mobius.bmlvcgen.vcgen.exceptions.TranslationException;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * Superclass of expression translators.
 * Handles (or should handle) almost all operators.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <V> Type of visitor.
 */
public abstract class ExprTranslator<V> 
    implements ExprVisitor<V> {
  // Type of 'this' object.
  private final ObjectType thisType;
  
  // Type converter.
  private final TypeConverter typeConverter;
  
  // Last expression created by this translator.
  private Term lastExpr;
  
  // BCEL type of last expression.
  private org.apache.bcel.generic.Type lastType;
  
  // Are we inside an \\old annotation?
  private boolean old;
  
  // Stack used to store names of quantified
  // variables.
  private final List<QuantVariable> qvars;
  
  // Another stack for quant vars bcel types.
  private final List<org.apache.bcel.generic.Type> qtypes;
  
  /**
   * Constructor.
   * @param thisType Type of 'this' object.
   * @param old Is the expression inside '\\old' ?
   */
  protected ExprTranslator(final ObjectType thisType, 
                           final boolean old) {
    typeConverter = new TypeConverter();
    this.thisType = thisType;
    this.old = old;
    qvars = new ArrayList<QuantVariable>();
    qtypes = new ArrayList<org.apache.bcel.generic.Type>();
  }
  
  /**
   * Return this pointer.
   * @return This pointer.
   */
  protected abstract V getThis();
  
  // NOTE: In this class lastExpr is accessed directly.
  
  /**
   * Get last expression visited by this translator.
   * @return Translated expression.
   */
  public final Term getLastExpr() {
    return lastExpr;
  }
  
  /**
   * Set translated expression.
   * @param expr Translated expression.
   */
  protected final void setLastExpr(final Term expr) {
    lastExpr = expr;
  }
  
  /**
   * Get heap variable. If old is set, this
   * returns a reference to old heap.
   * @return Heap term.
   */
  protected QuantVariableRef getCurrentHeap() {
    if (old) {
      return Heap.varPre;
    } else {
      return Heap.var;
    }
  }
  
  /**
   * Get object used to convert types.
   * @return Type converter.
   */
  protected TypeConverter getTypeConverter() {
    return typeConverter;
  }
  
  /**
   * Are we processing old expression?
   * @return .
   */
  protected boolean isOld() {
    return old;
  }
  
  /**
   * Get BCEL type of last visited expression.
   * @return Type.
   */
  public org.apache.bcel.generic.Type getLastType() {
    return lastType;
  }
  
  /**
   * Set expression type.
   * @param type Type.
   */
  protected void setLastType(
      final org.apache.bcel.generic.Type type) {
    lastType = type;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void arrayAccess(final Expr array, final Expr index) {
    final QuantVariableRef heap = getCurrentHeap();
    array.accept(getThis());
    final Term left = lastExpr;
    if (!(lastType instanceof ArrayType)) {
      throw new TranslationException(
        "Non-array type treated as array");
    }
    final ArrayType arrayType = (ArrayType)lastType;
    final Sort type = Type.getSort(arrayType.getElementType());
    index.accept(getThis());
    final Term idx = lastExpr;
    
    lastExpr = Heap.selectArray(heap, left, idx, type);
    lastType = arrayType.getElementType();
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void arrayLength(final Expr array) {
    final QuantVariableRef heap = getCurrentHeap();
    array.accept(getThis());
    final Term left = lastExpr;
    final Sort fieldType = Num.sortInt;
    final QuantVariable fld = Expression.length;
    lastExpr = Heap.select(heap, left, fld, fieldType);
    lastType = org.apache.bcel.generic.Type.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void call(final Expr obj, 
            final MethodName method, 
            final Expr... args) {
    // TODO: Method calls in specifications.
    throw new TranslationException();
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void cond(final Expr cnd, 
            final Expr ifTrue, 
            final Expr ifFalse) {
    // TODO: :-((((((((((((((((((((((
    throw new TranslationException();
  }
  
  /** {@inheritDoc} */
  public void constNull() {
    lastExpr = Ref.nullValue();
    lastType = ObjectType.NULL;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void getField(final Expr obj, 
                final String field,
                final mobius.bmlvcgen.bml.types.Type type) {
    final QuantVariableRef heap = getCurrentHeap();
    obj.accept(getThis());
    final Term left = lastExpr;
    if (!(lastType instanceof ObjectType)) {
      throw new TranslationException(
        "Non-object type treated as object");
    }
    final ObjectType objType = (ObjectType)lastType;
    type.accept(typeConverter);
    final Sort fieldType = Type.getSort(typeConverter.getType());
    // TODO: Find cleaner way to do this.

    final QuantVariable fld = 
      ExprHelper.getFieldVar(objType, field);
    lastExpr = Heap.select(heap, left, fld, fieldType);
    lastType = typeConverter.getType();
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void getField(final String field, 
                final mobius.bmlvcgen.bml.types.Type type) {
    final QuantVariableRef heap = getCurrentHeap();
    final Term left = Ref.varThis;
    type.accept(typeConverter);
    final Sort fieldType = Type.getSort(typeConverter.getType());
    // TODO: Find cleaner way to do this.
    final QuantVariable fld = 
      ExprHelper.getFieldVar(thisType, field);
    lastExpr = Heap.select(heap, left, fld, fieldType);
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void self() {
    lastExpr = Heap.valueToSort(Ref.varThis, Ref.sort);
    lastType = thisType;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolAnd(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    if (Logic.sort.equals(left.getSort()) ||
        Logic.sort.equals(right.getSort())) {
      lastExpr = Logic.and(Logic.boolToPred(left), 
                           Logic.boolToPred(right));
    } else {
      lastExpr = Bool.and(left, right);
    }
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public void boolConst(final boolean v) {
    lastExpr = Bool.value(v);
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolEquiv(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    if (Logic.sort.equals(left.getSort()) ||
        Logic.sort.equals(right.getSort())) {
      lastExpr = Logic.fullImplies(
                           Logic.boolToPred(left), 
                           Logic.boolToPred(right));
    } else {
      lastExpr = Bool.fullImplies(left, right);
    }
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolImpl(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    if (Logic.sort.equals(left.getSort()) ||
        Logic.sort.equals(right.getSort())) {
      lastExpr = Logic.implies(
                           Logic.boolToPred(left), 
                           Logic.boolToPred(right));
    } else {
      lastExpr = Bool.implies(left, right);
    }
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolInequiv(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    if (Logic.sort.equals(left.getSort()) ||
        Logic.sort.equals(right.getSort())) {
      lastExpr = Logic.not(
                   Logic.fullImplies(
                           Logic.boolToPred(left), 
                           Logic.boolToPred(right)));
    } else {
      lastExpr = Bool.not(Bool.fullImplies(left, right));
    }
    lastType = BasicType.BOOLEAN;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolNot(final Expr e) {

  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void boolOr(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    if (Logic.sort.equals(left.getSort()) ||
        Logic.sort.equals(right.getSort())) {
      lastExpr = Logic.or(
                           Logic.boolToPred(left), 
                           Logic.boolToPred(right));
    } else {
      lastExpr = Bool.or(left, right);
    }
    lastType = BasicType.BOOLEAN;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void boolRimpl(final Expr l, final Expr r) {
    boolImpl(r, l);
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void eq(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    if (Logic.sort.equals(left.getSort()) ||
        Logic.sort.equals(right.getSort())) {
      lastExpr = Logic.fullImplies(
                           Logic.boolToPred(left), 
                           Logic.boolToPred(right));
    } else {
      lastExpr = Bool.equals(left, right);
    }
    lastExpr = Logic.boolToPred(lastExpr);
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void ge(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Bool.ge(left, right);
    lastExpr = Logic.boolToPred(lastExpr);
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void gt(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Bool.gt(left, right);
    lastExpr = Logic.boolToPred(lastExpr);
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void isSubtype(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Logic.typeLE(left, right);
    lastExpr = Logic.boolToPred(lastExpr);
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void le(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Bool.le(left, right);
    lastExpr = Logic.boolToPred(lastExpr);
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void lt(final Expr l, final Expr r) {
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Bool.lt(left, right);
    lastExpr = Logic.boolToPred(lastExpr);
    lastType = BasicType.BOOLEAN;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void neq(final Expr l, final Expr r) {
    eq(l, r);
    if (Logic.sort.equals(lastExpr.getSort())) {
      lastExpr = Logic.not(lastExpr);
    } else {
      lastExpr = Bool.not(lastExpr);
    }
    lastExpr = Logic.boolToPred(lastExpr);
    lastType = BasicType.BOOLEAN;
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void add(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Num.add(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void bitAnd(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Expression.bitand(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void bitNeg(final Expr e) {
    e.accept(getThis());
    lastExpr = Num.bitnot(lastExpr);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void bitOr(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Expression.bitor(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>>
  void bitXor(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Expression.bitxor(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public void byteConst(final byte v) {
    lastExpr = Num.value(v);
    lastType = BasicType.BYTE;
  }

  /** {@inheritDoc} */
  public void charConst(final char v) {
    lastExpr = Num.value(v);
    lastType = BasicType.CHAR;
  }

  /** {@inheritDoc} */
  public void intConst(final int v) {
    lastExpr = Num.value(v);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void intDiv(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Num.div(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public void longConst(final long v) {
    lastExpr = Num.value(v);
    lastType = BasicType.LONG;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void minus(final Expr e) {
    // TODO: Non-integer arithmetic.
    e.accept(getThis());
    lastExpr = Num.sub(lastExpr);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void mod(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Num.mod(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void mul(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Num.mul(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void sar(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Num.rshift(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void shl(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Num.lshift(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public void shortConst(final short v) {
    lastExpr = Num.value(v);
    lastType = BasicType.SHORT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void shr(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Num.urshift(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void sub(final Expr l, final Expr r) {
    // TODO: Non-integer arithmetic.
    l.accept(getThis());
    final Term left = lastExpr;
    r.accept(getThis());
    final Term right = lastExpr;
    lastExpr = Num.sub(left, right);
    lastType = BasicType.INT;
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void cast(final mobius.bmlvcgen.bml.types.Type type,
            final Expr e) {
    // TODO: Casts
    throw new TranslationException("Casts are not supported");
  }

  /** {@inheritDoc} */
  public void typeConst(
      final mobius.bmlvcgen.bml.types.Type type) {
    // TODO: Types...
  }

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void exists(final Expr expr, 
                     final String varName, 
                     final mobius.bmlvcgen.bml.types.Type type) {
    final QuantVariable var = quantBegin(varName, type);
    expr.accept(getThis());
    if (!Logic.sort.equals(lastExpr.getSort())) {
      lastExpr = Logic.boolToPred(lastExpr);
    }
    lastExpr = Logic.exists(var, lastExpr);
    quantEnd();    
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super V>> 
  void forall(final Expr expr, 
              final String varName,
              final mobius.bmlvcgen.bml.types.Type type) {
    final QuantVariable var = quantBegin(varName, type);
    expr.accept(getThis());
    if (!Logic.sort.equals(lastExpr.getSort())) {
      lastExpr = Logic.boolToPred(lastExpr);
    }
    lastExpr = Logic.forall(var, lastExpr);
    quantEnd();
  }
  
  
  /** {@inheritDoc} */
  public void boundvar(final int level) {
    final QuantVariable var = qvars.get(level);
    lastExpr = Expression.rvar(var);
    lastType = qtypes.get(level);
  }

  private QuantVariable quantBegin(
      final String varName,
      final mobius.bmlvcgen.bml.types.Type type) {
    type.accept(typeConverter);
    final Sort sort = Type.getSort(typeConverter.getType());
    final QuantVariable var;
    if (varName == null) {
      var = Expression.var(sort);
    } else {
      var = Expression.var(sortPrefix(sort) +
                           "_" + varName, sort);
    }
    qtypes.add(0, typeConverter.getType());
    qvars.add(0, var);
    return var;
  }

  private void quantEnd() {
    qvars.remove(0);
    lastType = BasicType.BOOLEAN;
  }
  
  // Type prefix added to variable names.
  private static String sortPrefix(final Sort sort) {
    final String result;
    
    if (Num.sortInt.equals(sort)) {
      result = "i";
    } else if (Num.sortReal.equals(sort)) {
      result = "f";
    } else if (Ref.sort.equals(sort)) {
      result = "r";
    } else if (Bool.sort.equals(sort)) {
      result = "b";
    } else {
      result = "x";
    }
    return result;
  }
  
}
