package b2bpl.translation;

import static b2bpl.translation.CodeGenerator.add;
import static b2bpl.translation.CodeGenerator.alive;
import static b2bpl.translation.CodeGenerator.arrayAccess;
import static b2bpl.translation.CodeGenerator.arrayLength;
import static b2bpl.translation.CodeGenerator.bitAnd;
import static b2bpl.translation.CodeGenerator.bitOr;
import static b2bpl.translation.CodeGenerator.bitShl;
import static b2bpl.translation.CodeGenerator.bitShr;
import static b2bpl.translation.CodeGenerator.bitUShr;
import static b2bpl.translation.CodeGenerator.bitXor;
import static b2bpl.translation.CodeGenerator.divide;
import static b2bpl.translation.CodeGenerator.elementType;
import static b2bpl.translation.CodeGenerator.exists;
import static b2bpl.translation.CodeGenerator.fieldAccess;
import static b2bpl.translation.CodeGenerator.forall;
import static b2bpl.translation.CodeGenerator.greater;
import static b2bpl.translation.CodeGenerator.greaterEqual;
import static b2bpl.translation.CodeGenerator.icast;
import static b2bpl.translation.CodeGenerator.implies;
import static b2bpl.translation.CodeGenerator.int2bool;
import static b2bpl.translation.CodeGenerator.isEqual;
import static b2bpl.translation.CodeGenerator.isEquiv;
import static b2bpl.translation.CodeGenerator.isInstanceOf;
import static b2bpl.translation.CodeGenerator.isSubtype;
import static b2bpl.translation.CodeGenerator.ival;
import static b2bpl.translation.CodeGenerator.less;
import static b2bpl.translation.CodeGenerator.lessEqual;
import static b2bpl.translation.CodeGenerator.logicalAnd;
import static b2bpl.translation.CodeGenerator.logicalNot;
import static b2bpl.translation.CodeGenerator.logicalOr;
import static b2bpl.translation.CodeGenerator.modulo;
import static b2bpl.translation.CodeGenerator.multiply;
import static b2bpl.translation.CodeGenerator.notEqual;
import static b2bpl.translation.CodeGenerator.quantVarName;
import static b2bpl.translation.CodeGenerator.rval;
import static b2bpl.translation.CodeGenerator.sub;
import static b2bpl.translation.CodeGenerator.typ;
import static b2bpl.translation.CodeGenerator.type;
import static b2bpl.translation.CodeGenerator.val;
import static b2bpl.translation.CodeGenerator.var;

import java.util.ArrayList;
import java.util.List;

import b2bpl.bpl.ast.BPLBoolLiteral;
import b2bpl.bpl.ast.BPLExpression;
import b2bpl.bpl.ast.BPLIntLiteral;
import b2bpl.bpl.ast.BPLLogicalNotExpression;
import b2bpl.bpl.ast.BPLNullLiteral;
import b2bpl.bpl.ast.BPLUnaryMinusExpression;
import b2bpl.bpl.ast.BPLVariable;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.BMLExpressionVisitor;
import b2bpl.bytecode.bml.ast.BMLArrayAccessExpression;
import b2bpl.bytecode.bml.ast.BMLArrayLengthExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryBitwiseExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryLogicalExpression;
import b2bpl.bytecode.bml.ast.BMLBooleanLiteral;
import b2bpl.bytecode.bml.ast.BMLBoundVariableExpression;
import b2bpl.bytecode.bml.ast.BMLCastExpression;
import b2bpl.bytecode.bml.ast.BMLElemTypeExpression;
import b2bpl.bytecode.bml.ast.BMLEqualityExpression;
import b2bpl.bytecode.bml.ast.BMLExpression;
import b2bpl.bytecode.bml.ast.BMLFieldAccessExpression;
import b2bpl.bytecode.bml.ast.BMLFieldExpression;
import b2bpl.bytecode.bml.ast.BMLFreshExpression;
import b2bpl.bytecode.bml.ast.BMLInstanceOfExpression;
import b2bpl.bytecode.bml.ast.BMLIntLiteral;
import b2bpl.bytecode.bml.ast.BMLLocalVariableExpression;
import b2bpl.bytecode.bml.ast.BMLLogicalNotExpression;
import b2bpl.bytecode.bml.ast.BMLNullLiteral;
import b2bpl.bytecode.bml.ast.BMLOldExpression;
import b2bpl.bytecode.bml.ast.BMLPredicate;
import b2bpl.bytecode.bml.ast.BMLQuantifierExpression;
import b2bpl.bytecode.bml.ast.BMLRelationalExpression;
import b2bpl.bytecode.bml.ast.BMLResultExpression;
import b2bpl.bytecode.bml.ast.BMLStackCounterExpression;
import b2bpl.bytecode.bml.ast.BMLStackElementExpression;
import b2bpl.bytecode.bml.ast.BMLThisExpression;
import b2bpl.bytecode.bml.ast.BMLTypeOfExpression;
import b2bpl.bytecode.bml.ast.BMLUnaryMinusExpression;


/**
 * A translator for BML specifications.
 *
 * <p>
 * This translator can be used to translate BML specification expressions
 * appearing in a whole variety of contexts:
 * <ul>
 *   <li>in object invariants</li>
 *   <li>in method specifications (pre-/post-/exceptional-post-conditions)</li>
 *   <li>in local instruction annotations (assertions, assumptions, ...)</li>
 *   <li>in loop specifications</li>
 * </ul>
 * The translator must be parameterized with the names of the variables relevant
 * to the context in which the BML specification appears. Since this
 * parameterization differs significantly, specialized factory methods are
 * provided for constructing translators for the different contexts.
 * </p>
 *
 * @author Ovidio Mallo
 */
public class SpecificationTranslator {

  /**
   * The translation context to be used during the translation of the current
   * BML specification.
   */
  private TranslationContext context;

  /** The name of current heap to use in the translation. */
  protected final String heap;

  /** The name of old heap to use in the translation. */
  protected final String oldHeap;

  /** The name of the variable representing the this object. */
  protected final String thisReference;

  /** The name of the variable representing a method's return value. */
  protected final String result;

  /** The names of the local variables to us in the translation. */
  protected final String[] localVariables;

  /** The names of the stack variables to use in the translation. */
  protected final String[] stackElements;

  /** The names of the old local variables to use in the translation. */
  protected final String[] oldLocalVariables;

  /**
   * A list of the currently active bound variables. When translating an
   * exceptional postcondition, BML treats the exception object thrown as a
   * bound variable, so it will also be included in this list. Other bound
   * variables originate from BML quantifier expressions.
   */
  protected final List<String> boundVariables = new ArrayList<String>();

  /**
   * Constructor with all the possible parameterizations of a specification
   * translator.
   *
   * @param heap               The name of the current heap variable.
   * @param oldHeap            The name of the old heap variable.
   * @param thisReference      The name of the variable representing the this
   *                           object.
   * @param resultOrException  The name of the variable representing the
   *                           method's return value inside a normal
   *                           postcondition, or else, the exception object
   *                           thrown inside an exceptional postcondition.
   * @param localVariables     The names of the local variables.
   * @param stackElements      The names of the stack variables.
   * @param oldLocalVariables  The names of the old local variables.
   */
  protected SpecificationTranslator(
      String heap,
      String oldHeap,
      String thisReference,
      String resultOrException,
      String[] localVariables,
      String[] stackElements,
      String[] oldLocalVariables) {
    this.heap = heap;
    this.oldHeap = oldHeap;
    this.thisReference = thisReference;
    this.result = resultOrException;
    this.localVariables = localVariables;
    this.stackElements = stackElements;
    this.oldLocalVariables = oldLocalVariables;
    // If the resultOrException is the exception object thrown as referenced in
    // a method's exceptional postcondition, it is treated in BML as a bound
    // variable with index 0, so we add it to the list of bound variables right
    // from the beginning.
    boundVariables.add(resultOrException);
  }

  /**
   * Static factory method for creating a specification translator appropriate
   * for translating object invariants.
   *
   * @param heap           The name of the current heap variable.
   * @param thisReference  The name of the variable representing the this
   *                       object.
   * @return               A specification translator for translating object
   *                       invariants.
   */
  public static SpecificationTranslator forInvariant(
      String heap,
      String thisReference) {
    return new SpecificationTranslator(
        heap,
        null,
        thisReference,
        null,
        null,
        null,
        null);
  }

  /**
   * Static factory method for creating a specification translator appropriate
   * for translating method preconditions.
   *
   * @param heap        The name of the current heap variable.
   * @param parameters  The names of the method's parameters.
   * @return            A specification translator for translating method
   *                    preconditions.
   */
  public static SpecificationTranslator forPrecondition(
      String heap,
      String[] parameters) {
    return new SpecificationTranslator(
        heap,
        null,
        // Extract the potential this object from the parameters.
        (parameters.length == 0) ? null : parameters[0],
        null,
        parameters,
        null,
        null);
  }
  
  /**
   * Static factory method for creating a specification translator appropriate
   * for translating modifies varialbes .
   *
   * @param heap        The name of the current heap variable.
   * @param parameters  The names of the method's parameters.
   * @return            A specification translator for translating method's
   *                    modifies variables.
   */
  public static SpecificationTranslator forModifiesClause(
      String heap,
      String[] parameters) {
    return new SpecificationTranslator(
        heap,
        null,
        // Extract the potential this object from the parameters.
        (parameters.length == 0) ? null : parameters[0],
        null,
        null,
        null,
        null);
  }

  /**
   * Static factory method for creating a specification translator appropriate
   * for translating normal or exceptional method postconditions.
   *
   * @param heap               The name of the current heap variable.
   * @param oldHeap            The name of the old heap variable.
   * @param resultOrException  The name of the variable representing the
   *                           method's return value inside a normal
   *                           postcondition, or else, the exception object
   *                           thrown inside an exceptional postcondition.
   * @param parameters         The names of the method's parameters.
   * @return                   A specification translator for translating normal
   *                           or exceptional method postconditions.
   */
  public static SpecificationTranslator forPostcondition(
      String heap,
      String oldHeap,
      String resultOrException,
      String[] parameters) {
    return new SpecificationTranslator(
        heap,
        oldHeap,
        // Extract the potential this object from the parameters.
        (parameters.length == 0) ? null : parameters[0],
        resultOrException,
        parameters,
        null,
        parameters);
  }

  /**
   * Static factory method for creating a specification translator appropriate
   * for translating local BML annotations attached to instructions such as
   * assertions, loop specifications, ....
   *
   * @param heap            The name of the current heap variable.
   * @param oldHeap         The name of the old heap variable.
   * @param localVariables  The names of the local variables.
   * @param stackElements   The names of the stack variables.
   * @param parameters      The parameter names of the method in which the
   *                        specification appears (used as the old local
   *                        variables).
   * @return                A specification translator for translating local
   *                        specifications.
   */
  public static SpecificationTranslator forLocalSpecification(
      String heap,
      String oldHeap,
      String[] localVariables,
      String[] stackElements,
      String[] parameters) {
    return new SpecificationTranslator(
        heap,
        oldHeap,
        // Extract the potential this object from the parameters.
        (parameters.length == 0) ? null : parameters[0],
        null,
        localVariables,
        stackElements,
        parameters);
  }

  /**
   * Performs the actual translation of the given BML {@code specification}
   * and returns a BoogiePL expression representing it.
   *
   * @param context        The {@code TranslationContext} to be used for
   *                       translating type/field/constant/... references.
   * @param specification  The specification to be translated.
   * @return               The BoogiePL expression resulting from the 
   *                       translation of the given BML specification.
   */
  public BPLExpression translate(
      TranslationContext context,
      BMLExpression specification) {
    this.context = context;
    BPLExpression bplExpr = specification.accept(new Translator());

    // Since boolean variables are mapped to int variables in the BoogiePL
    // program, we must explicitly convert them to BoogiePL bool values
    // whenever they are used as predicates.
    if ((specification instanceof BMLPredicate) && !specification.isPredicate()) {
      bplExpr = int2bool(bplExpr);
    }

    return bplExpr;
  }

  /**
   * The visitor performing the actual translation of the BML specification.
   *
   * @author Ovidio Mallo
   */
  private final class Translator
      implements BMLExpressionVisitor<BPLExpression> {

    /**
     * State variable to keep track of whether we currently are inside a BML
     * \old expression. This is the case if and only if {@code insideOld}
     * &gt; 0. The reason why we do not use a simple flag but a counter instead
     * is to support possibly nested \old expressions.
     */
    private int insideOld = 0;

    /**
     * Returns the name of the heap variable to be used in the current context
     * of the translation. The actual heap to be used thereby depends on whether
     * we currently are inside a BML \old expression or not.
     *
     * @return  The name of the heap variable to be used in the current context
     *          of the translation.
     */
    private String getHeap() {
      return (insideOld > 0) ? oldHeap : heap;
    }

    /**
     * Returns the name of the local variable for the given {@code index}
     * to be used in the current context of the translation. The actual local
     * variable to be used thereby depends on whether we currently are inside a
     * BML \old expression or not.
     *
     * @param index  The index of the local variable.
     * @return       The name of the local variable for the given
     *               {@code index} to be used in the current context of the
     *               translation.
     */
    private String getLocalVariable(int index) {
      if (insideOld > 0) {
        return oldLocalVariables[index];
      }
      return localVariables[index];
    }

    /**
     * Returns the name of the bound variable for the given {@code index}
     * to be used in the current context of the translation.
     *
     * @param index  The index of the bound variable.
     * @return       The name of the bound variable for the given
     *               {@code index} to be used in the current context of the
     *               translation.     
     */
    private String getBoundVariable(int index) {
      return boundVariables.get(index);
    }

    /**
     * Adds <code>count</count> new bound variables to the current context of
     * the translation. The new variables are given names which are unique the
     * current context.
     *
     * @param count  The number of new bound variables to add to the current
     *               context of the translation.
     */
    private void addBoundVariables(int count) {
      for (int i = 0; i < count; i++) {
        boundVariables.add(i, quantVarName("bv") + boundVariables.size());
      }
    }

    /**
     * Removes the <code>count</count> bound variables last added to the current
     * context of the translation.
     *
     * @param count  The number of bound variables to remove from the current
     *               context of the translation.
     */
    private void removeBoundVariables(int count) {
      for (int i = 0; i < count; i++) {
        boundVariables.remove(0);
      }
    }

    public BPLExpression visitQuantifierExpression(BMLQuantifierExpression expr) {
      JType[] bvTypes = expr.getVariableTypes();

      // Add the new bound variables to the context of the translation.
      addBoundVariables(bvTypes.length);
      BPLExpression body = expr.getExpression().accept(this);

      BPLExpression bvTypeInfo = null;
      if (bvTypes.length > 0) {
        // Assume the bound variables are of the desired type.
        bvTypeInfo = isSubtype(
            typ(val(var(getBoundVariable(0)), bvTypes[0])),
            context.translateTypeReference(bvTypes[0]));
        for (int i = 1; i < bvTypes.length; i++) {
          bvTypeInfo = logicalAnd(
              bvTypeInfo,
              isSubtype(
                  typ(val(var(getBoundVariable(i)), bvTypes[i])),
                  context.translateTypeReference(bvTypes[i])));
        }
      }

      // Construct the variables for the BoogiePL quantifier expression. We must
      // do this before removing the bound variables from the current context of
      // the translation.
      BPLVariable[] variables = new BPLVariable[bvTypes.length];
      for (int i = 0; i < variables.length; i++) {
        variables[i] = new BPLVariable(getBoundVariable(i), type(bvTypes[i]));
      }

      // Now, we can remove the bound variables from the current context of the
      // translation.
      removeBoundVariables(bvTypes.length);

      // Finally, return the actual BoogiePL quantifier expression.
      switch (expr.getOperator()) {
        case FORALL:
          body = (bvTypeInfo == null) ? body : implies(bvTypeInfo, body);
          return forall(variables, body);
        case EXISTS:
        default:
          body = (bvTypeInfo == null) ? body : logicalAnd(bvTypeInfo, body);
          return exists(variables, body);
      }
    }

    public BPLExpression visitBinaryArithmeticExpression(
        BMLBinaryArithmeticExpression expr) {
      BPLExpression left = expr.getLeft().accept(this);
      BPLExpression right = expr.getRight().accept(this);

      switch (expr.getOperator()) {
        case PLUS:
          return add(left, right);
        case MINUS:
          return sub(left, right);
        case TIMES:
          return multiply(left, right);
        case DIVIDE:
          return divide(left, right);
        case REMAINDER:
        default:
          return modulo(left, right);
      }
    }

    public BPLExpression visitBinaryLogicalExpression(
        BMLBinaryLogicalExpression expr) {
      BPLExpression left = expr.getLeft().accept(this);
      BPLExpression right = expr.getRight().accept(this);

      // Since boolean variables are mapped to int variables in the BoogiePL
      // program, we must explicitly convert them to BoogiePL bool values
      // whenever they are used as predicates.
      left = expr.getLeft().isPredicate() ? left : int2bool(left);
      right = expr.getRight().isPredicate() ? right : int2bool(right);

      switch (expr.getOperator()) {
        case AND:
          return logicalAnd(left, right);
        case OR:
          return logicalOr(left, right);
        case IMPLIES:
          return implies(left, right);
        case EQUIVALENCE:
        default:
          return isEquiv(left, right);
      }
    }

    public BPLExpression visitEqualityExpression(BMLEqualityExpression expr) {
      BPLExpression left = expr.getLeft().accept(this);
      BPLExpression right = expr.getRight().accept(this);

      // Since boolean variables are mapped to int variables in the BoogiePL
      // program, they may be compared to BoogiePL predicates of type bool which
      // would lead to a semantic error. Therefore, if we detect such a
      // situation, we explicitly convert the int value to a bool.
      // Note that we should not convert the predicate to an int since
      // quantifiers in BoogiePL cannot be used as terms.
      if (!expr.getLeft().isPredicate() && expr.getRight().isPredicate()) {
        left = int2bool(left);
      } else if (expr.getLeft().isPredicate()
                 && !expr.getRight().isPredicate()) {
        right = int2bool(right);
      }

      switch (expr.getOperator()) {
        case EQUALS:
          return isEqual(left, right);
        case NOT_EQUALS:
        default:
          return notEqual(left, right);
      }
    }

    public BPLExpression visitRelationalExpression(
        BMLRelationalExpression expr) {
      BPLExpression left = expr.getLeft().accept(this);
      BPLExpression right = expr.getRight().accept(this);

      switch (expr.getOperator()) {
        case LESS:
          return less(left, right);
        case GREATER:
          return greater(left, right);
        case LESS_EQUAL:
          return lessEqual(left, right);
        case GREATER_EQUAL:
        default:
          return greaterEqual(left, right);
      }
    }

    public BPLExpression visitBinaryBitwiseExpression(
        BMLBinaryBitwiseExpression expr) {
      BPLExpression left = expr.getLeft().accept(this);
      BPLExpression right = expr.getRight().accept(this);

      switch (expr.getOperator()) {
        case SHL:
          return bitShl(left, right);
        case SHR:
          return bitShr(left, right);
        case USHR:
          return bitUShr(left, right);
        case AND:
          return bitAnd(left, right);
        case OR:
          return bitOr(left, right);
        case XOR:
        default:
          return bitXor(left, right);
      }
    }

    public BPLExpression visitUnaryMinusExpression(
        BMLUnaryMinusExpression expr) {
      BPLExpression expression = expr.getExpression().accept(this);
      return new BPLUnaryMinusExpression(expression);
    }

    public BPLExpression visitLogicalNotExpression(
        BMLLogicalNotExpression expr) {
      BPLExpression expression = expr.getExpression().accept(this);
      // Since boolean variables are mapped to int variables in the BoogiePL
      // program, we must explicitly convert them to BoogiePL bool values
      // whenever they are used as predicates.
      if (!expr.getExpression().isPredicate()) {
        expression = int2bool(expression);
      }
      return new BPLLogicalNotExpression(expression);
    }

    public BPLExpression visitInstanceOfExpression(
        BMLInstanceOfExpression expr) {
      return isInstanceOf(
          rval(expr.getExpression().accept(this)),
          context.translateTypeReference(expr.getTargetType()));
    }

    public BPLExpression visitCastExpression(BMLCastExpression expr) {
      BPLExpression expression = expr.getExpression().accept(this);
      JType type = expr.getTargetType();
      if (expr.getTargetType().isBaseType()) {
        return icast(expression, context.translateClassLiteral(type));
      }
      // There is no need to do anything if we are casting to a reference type.
      return expression;
    }

    public BPLExpression visitBooleanLiteral(BMLBooleanLiteral literal) {
      if (literal == BMLBooleanLiteral.TRUE) {
        return BPLBoolLiteral.TRUE;
      } else {
        return BPLBoolLiteral.FALSE;
      }
    }

    public BPLExpression visitIntLiteral(BMLIntLiteral literal) {
      return context.translateIntLiteral(literal.getValue());
    }

    public BPLExpression visitNullLiteral(BMLNullLiteral literal) {
      return BPLNullLiteral.NULL;
    }

    public BPLExpression visitLocalVariableExpression(
        BMLLocalVariableExpression expr) {
      return var(getLocalVariable(expr.getIndex()));
    }

    public BPLExpression visitBoundVariableExpression(
        BMLBoundVariableExpression expr) {
      return var(getBoundVariable(expr.getIndex()));
    }

    public BPLExpression visitStackElementExpression(
        BMLStackElementExpression expr) {
      return var(stackElements[expr.getIndex()]);
    }

    public BPLExpression visitStackCounterExpression(
        BMLStackCounterExpression expr) {
      return new BPLIntLiteral(expr.getCounter());
    }

    public BPLExpression visitOldExpression(BMLOldExpression expr) {
      insideOld++;
      BPLExpression result = expr.getExpression().accept(this);
      insideOld--;
      return result;
    }

    public BPLExpression visitPredicate(BMLPredicate predicate) {
      return predicate.getExpression().accept(this);
    }

    public BPLExpression visitFieldExpression(BMLFieldExpression expr) {
      BCField field = expr.getField();
      if (field.isStatic()) {
        return fieldAccess(context, getHeap(), null, field);
      }
      return fieldAccess(context, getHeap(), var(thisReference), field);
    }

    public BPLExpression visitFieldAccessExpression(
        BMLFieldAccessExpression expr) {
      BCField field = expr.getField();
      if (field.isStatic()) {
        // If the field is static, we ignore the prefix of the field access
        // expression.
        return fieldAccess(context, getHeap(), null, field);
      }
      BPLExpression prefix = expr.getPrefix().accept(this);
      return fieldAccess(context, getHeap(), prefix, field);
    }

    public BPLExpression visitArrayAccessExpression(
        BMLArrayAccessExpression expr) {
      BPLExpression prefix = expr.getPrefix().accept(this);
      BPLExpression index = expr.getIndex().accept(this);
      JArrayType arrayType = (JArrayType) expr.getPrefix().getType();
      return arrayAccess(getHeap(), arrayType, prefix, index);
    }

    public BPLExpression visitArrayLengthExpression(
        BMLArrayLengthExpression expr) {
      BPLExpression prefix = expr.getPrefix().accept(this);
      return arrayLength(rval(prefix));
    }

    public BPLExpression visitTypeOfExpression(BMLTypeOfExpression expr) {
      BPLExpression typeExpr = expr.getExpression().accept(this);
      if (expr.getExpression().getType().isReferenceType()) {
        return typ(rval(typeExpr));
      }
      return typ(ival(typeExpr));
    }

    public BPLExpression visitElemTypeExpression(BMLElemTypeExpression expr) {
      BPLExpression typeExpr = expr.getTypeExpression().accept(this);
      return elementType(typeExpr);
    }

    public BPLExpression visitResultExpression(BMLResultExpression expr) {
      return var(result);
    }

    public BPLExpression visitThisExpression(BMLThisExpression expr) {
      return var(thisReference);
    }

    public BPLExpression visitFreshExpression(BMLFreshExpression expr) {
      BPLExpression expression = expr.getExpression().accept(this);
      return logicalNot(alive(rval(expression), var(oldHeap)));
    }
  }
}
