package b2bpl.translation;

import static b2bpl.translation.CodeGenerator.arrayLength;
import static b2bpl.translation.CodeGenerator.arrayLoc;
import static b2bpl.translation.CodeGenerator.fieldAccess;
import static b2bpl.translation.CodeGenerator.fieldLoc;
import static b2bpl.translation.CodeGenerator.forall;
import static b2bpl.translation.CodeGenerator.get;
import static b2bpl.translation.CodeGenerator.implies;
import static b2bpl.translation.CodeGenerator.less;
import static b2bpl.translation.CodeGenerator.lessEqual;
import static b2bpl.translation.CodeGenerator.logicalAnd;
import static b2bpl.translation.CodeGenerator.notEqual;
import static b2bpl.translation.CodeGenerator.quantVarName;
import static b2bpl.translation.CodeGenerator.rval;
import static b2bpl.translation.CodeGenerator.toref;
import static b2bpl.translation.CodeGenerator.var;
import b2bpl.bpl.ast.BPLBoolLiteral;
import b2bpl.bpl.ast.BPLBuiltInType;
import b2bpl.bpl.ast.BPLExpression;
import b2bpl.bpl.ast.BPLVariable;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.bml.IBMLStoreRefVisitor;
import b2bpl.bytecode.bml.ast.BMLArrayAllStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayElementStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayRangeStoreRef;
import b2bpl.bytecode.bml.ast.BMLEverythingStoreRef;
import b2bpl.bytecode.bml.ast.BMLFieldAccessStoreRef;
import b2bpl.bytecode.bml.ast.BMLFieldStoreRef;
import b2bpl.bytecode.bml.ast.BMLLocalVariableStoreRef;
import b2bpl.bytecode.bml.ast.BMLNothingStoreRef;
import b2bpl.bytecode.bml.ast.BMLStoreRef;
import b2bpl.bytecode.bml.ast.BMLThisStoreRef;


/**
 * A translator for BML store references.
 *
 * <p>
 * This translator can be used to translate BML store references to a BoogiePL
 * predicate which is true if and only if a given location does <i>not</i>
 * refer to <i>any</i> of the BML store references of a modifies clause.
 * The translator supports method as well as loop modifies clauses and it must
 * be parameterized with the names of the variables relevant to the context in
 * which the modifies clause appears. Since this parameterization is different
 * for method and loop modifies clauses, specialized factory methods are
 * provided for constructing translators for the two contexts.
 * </p>
 *
 * @author Ovidio Mallo
 */
public class ModifiesFilter {

  /**
   * The {@code SpecificationTranslator} to be used for translating
   * BML specification expressions which may for example appear as the index of
   * an array store reference.
   */
  protected final SpecificationTranslator specTranslator;

  /**
   * The name of the variable representing the location in the heap containing
   * the store references of the modifies clause.
   */
  protected final String location;

  /**
   * The translation context to be used during the translation of the current
   * BML store reference.
   */
  private ITranslationContext context;

  /**
   * Constructor with all the possible parameterizations of a modifies clause
   * filter.
   *
   * @param heap               The name of the current heap variable.
   * @param oldHeap            The name of the old heap variable.
   * @param thisReference      The name of the variable representing the this
   *                           object.
   * @param localVariables     The names of the local variables.
   * @param stackElements      The names of the stack variables.
   * @param oldLocalVariables  The names of the old local variables.
   * @param location           The name of the variable representing the
   *                           location in the heap containing the store
   *                           references of the modifies clause.
   */
  protected ModifiesFilter(
      String heap,
      String oldHeap,
      String thisReference,
      String[] localVariables,
      String[] stackElements,
      String[] oldLocalVariables,
      String location) {
    this.specTranslator = new SpecificationTranslator(
        heap,
        oldHeap,
        thisReference,
        null,
        localVariables,
        stackElements,
        oldLocalVariables);
    this.location = location;
  }

  /**
   * Static factory method for creating a filter for method modifies clauses.
   *
   * @param heap        The name of the current heap variable.
   * @param parameters  The names of the method's parameter variables.
   * @param location    The name of the variable representing the location in
   *                    the heap containing the store references of the modifies
   *                    clause.
   */
  public static ModifiesFilter forMethod(
      String heap,
      String[] parameters,
      String location) {
    return new ModifiesFilter(
        heap,
        null,
        // Extract the potential this object from the parameters.
        (parameters.length == 0) ? null : parameters[0],
        parameters,
        null,
        null,
        location);
  }

  /**
   * Static factory method for creating a filter for loop modifies clauses.
   *
   * @param heap            The name of the current heap variable.
   * @param oldHeap         The name of the old heap variable.
   * @param thisReference   The name of the variable representing the this
   *                        object.
   * @param localVariables  The names of the local variables.
   * @param stackElements   The names of the stack variables.
   * @param parameters      The parameter names of the method in which the
   *                        specification appears (used as the old local
   *                        variables).
   * @param location        The name of the variable representing the location
   *                        in the heap containing the store references of the
   *                        modifies clause.
   */
  public static ModifiesFilter forLoop(
      String heap,
      String oldHeap,
      String thisReference,
      String[] localVariables,
      String[] stackElements,
      String[] parameters,
      String location) {
    return new ModifiesFilter(
        heap,
        oldHeap,
        thisReference,
        localVariables,
        stackElements,
        parameters,
        location);
  }

  /**
   * Performs the actual translation of the given BML store references
   * and returns a BoogiePL predicate which is true if and only if the location
   * passed to the constructor of this class does <i>not</i> refer to <i>any</i>
   * of the store references provided here.
   *
   * @param context    The {@code TranslationContext} to be used for
   *                   translating type/field/constant/... references.
   * @param storeRefs  The specification to be translated.
   * @return           The BoogiePL predicate which filters out all the
   *                   locations corresponding to the given BML store
   *                   references.
   */
  public BPLExpression translate(
      ITranslationContext context,
      BMLStoreRef... storeRefs) {
    this.context = context;
    Filter filter = new Filter();
    BPLExpression[] expressions = new BPLExpression[storeRefs.length];
    for (int i = 0; i < storeRefs.length; i++) {
      expressions[i] = storeRefs[i].accept(filter);
    }
    return logicalAnd(expressions);
  }

  /**
   * The visitor performing the actual translation of the BML store references.
   *
   * @author Ovidio Mallo
   */
  private final class Filter implements IBMLStoreRefVisitor<BPLExpression> {

    /**
     * State variable to keep track of whether we currently are on the LHS of a
     * field/array access. This is the case if and only if {@code onLhs > 0}.
     */
    private int onLhs = 0;

    public BPLExpression visitEverythingStoreRef(
        BMLEverythingStoreRef storeRef) {
      return BPLBoolLiteral.FALSE;
    }

    public BPLExpression visitNothingStoreRef(BMLNothingStoreRef storeRef) {
      return BPLBoolLiteral.TRUE;
    }

    public BPLExpression visitThisStoreRef(BMLThisStoreRef storeRef) {
      if (onLhs > 0) {
        return var(specTranslator.thisReference);
      }
      // Local variables are only supported on the LHS of a field/array access,
      // so here we simply return true.
      return BPLBoolLiteral.TRUE;
    }

    public BPLExpression visitLocalVariableStoreRef(
        BMLLocalVariableStoreRef storeRef) {
      if (onLhs > 0) {
        return var(specTranslator.localVariables[storeRef.getIndex()]);
      }
      // Local variables are only supported on the LHS of a field/array access,
      // so here we simply return true.
      return BPLBoolLiteral.TRUE;
    }

    public BPLExpression visitFieldStoreRef(BMLFieldStoreRef storeRef) {
      BCField field = storeRef.getField();
      if (onLhs > 0) {
        // If we are on the LHS of a field/array access, we simply return a
        // normal field access expression.
        return fieldAccess(
            context,
            specTranslator.heap,
            var(specTranslator.thisReference),
            field);
      }
      // If we are not on the LHS of a field/array access, we must return an
      // expression stating that the given location does not correspond to the
      // BML store reference being filtered out.
      return notEqual(
          var(location),
          fieldLoc(context, var(specTranslator.thisReference), field));
    }

    public BPLExpression visitFieldAccessStoreRef(
        BMLFieldAccessStoreRef storeRef) {
      onLhs++;
      BPLExpression left = storeRef.getPrefix().accept(this);
      onLhs--;

      BCField field = storeRef.getField().getField();
      if (onLhs > 0) {
        // If we are on the LHS of a field/array access, we simply return a
        // normal field access expression.
        return fieldAccess(context, specTranslator.heap, left, field);
      }
      // If we are not on the LHS of a field/array access, we must return an
      // expression stating that the given location does not correspond to the
      // BML store reference being filtered out.
      return notEqual(var(location), fieldLoc(context, left, field));
    }

    public BPLExpression visitArrayElementStoreRef(
        BMLArrayElementStoreRef storeRef) {
      onLhs++;
      BPLExpression prefix = storeRef.getPrefix().accept(this);
      onLhs--;
      BPLExpression index =
        specTranslator.translate(context, storeRef.getIndex());

      if (onLhs > 0) {
        // If we are on the LHS of a field/array access, we simply return a
        // normal array access expression.
        return toref(get(var(specTranslator.heap), arrayLoc(prefix, index)));
      }
      // If we are not on the LHS of a field/array access, we must return an
      // expression stating that the given location does not correspond to the
      // BML store reference being filtered out.
      return notEqual(var(location), arrayLoc(prefix, index));
    }

    public BPLExpression visitArrayAllStoreRef(BMLArrayAllStoreRef storeRef) {
      onLhs++;
      BPLExpression prefix = storeRef.getPrefix().accept(this);
      onLhs--;

      // We should never be on the LHS of some field access since this is
      // currently not supported.
      String i = quantVarName("i");
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      return forall(
          iVar,
          implies(
              logicalAnd(
                  lessEqual(context.translateIntLiteral(0), var(i)),
                  less(var(i), arrayLength(rval(prefix)))),
              notEqual(var(location), arrayLoc(prefix, var(i)))));
    }

    public BPLExpression visitArrayRangeStoreRef(
        BMLArrayRangeStoreRef storeRef) {
      onLhs++;
      BPLExpression prefix = storeRef.getPrefix().accept(this);
      onLhs--;
      BPLExpression startIndex =
        specTranslator.translate(context, storeRef.getStartIndex());
      BPLExpression endIndex =
        specTranslator.translate(context, storeRef.getEndIndex());

      // We should never be on the LHS of some field access since this is
      // currently not supported.
      String i = quantVarName("i");
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      return forall(
          iVar,
          implies(
              logicalAnd(
                  lessEqual(startIndex, var(i)),
                  lessEqual(var(i), endIndex)),
              notEqual(var(location), arrayLoc(prefix, var(i)))));
    }
  }
}
