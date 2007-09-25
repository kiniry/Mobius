/** Public domain. */

package escjava.sortedProver.simplify;

import escjava.sortedProver.NodeBuilder;

/**
 * TODO: description
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class SimplifyNodeBuilder extends NodeBuilder {

  /* @see escjava.sortedProver.NodeBuilder#buildAnd(escjava.sortedProver.NodeBuilder.SPred[]) */
  @Override
  public SPred buildAnd(SPred[] args) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildAnyEQ(escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SAny) */
  @Override
  public SPred buildAnyEQ(SAny arg1, SAny arg2) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildAnyNE(escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SAny) */
  @Override
  public SPred buildAnyNE(SAny arg1, SAny arg2) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildArrSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt) */
  @Override
  public SValue buildArrSelect(SMap map, SRef obj, SInt idx) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildArrStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SValue) */
  @Override
  public SMap buildArrStore(SMap map, SRef obj, SInt idx, SValue val) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildAssignCompat(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SAny) */
  @Override
  public SPred buildAssignCompat(SMap map, SValue val, SAny type) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildBool(boolean) */
  @Override
  public SBool buildBool(boolean b) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildConstantRef(escjava.sortedProver.NodeBuilder.FnSymbol) */
  @Override
  public SAny buildConstantRef(FnSymbol c) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildDistinct(escjava.sortedProver.NodeBuilder.SAny[]) */
  @Override
  public SPred buildDistinct(SAny[] terms) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildDynSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny) */
  @Override
  public SValue buildDynSelect(SMap map, SRef obj, SAny field) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildDynStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SValue) */
  @Override
  public SMap buildDynStore(SMap map, SRef obj, SAny field, SValue val) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildExists(escjava.sortedProver.NodeBuilder.QuantVar[], escjava.sortedProver.NodeBuilder.SPred) */
  @Override
  public SPred buildExists(QuantVar[] vars, SPred body) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildFnCall(escjava.sortedProver.NodeBuilder.FnSymbol, escjava.sortedProver.NodeBuilder.SAny[]) */
  @Override
  public SAny buildFnCall(FnSymbol fn, SAny[] args) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildForAll(escjava.sortedProver.NodeBuilder.QuantVar[], escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.STerm[][], escjava.sortedProver.NodeBuilder.STerm[]) */
  @Override
  public SPred buildForAll(QuantVar[] vars, SPred body, STerm[][] pats,
    STerm[] nopats) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildITE(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SValue) */
  @Override
  public SValue buildITE(SPred cond, SValue then_part, SValue else_part) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildIff(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred) */
  @Override
  public SPred buildIff(SPred arg1, SPred arg2) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildImplies(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred) */
  @Override
  public SPred buildImplies(SPred arg1, SPred arg2) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildInt(long) */
  @Override
  public SInt buildInt(long n) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildIsTrue(escjava.sortedProver.NodeBuilder.SBool) */
  @Override
  public SPred buildIsTrue(SBool val) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildLabel(boolean, java.lang.String, escjava.sortedProver.NodeBuilder.SPred) */
  @Override
  public SPred buildLabel(boolean positive, String name, SPred pred) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildNewArray(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt) */
  @Override
  public SPred buildNewArray(SMap oldh, SAny type, SMap heap, SRef r, SInt len) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildNewObject(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef) */
  @Override
  public SPred buildNewObject(SMap oldh, SAny type, SMap heap, SRef r) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildNot(escjava.sortedProver.NodeBuilder.SPred) */
  @Override
  public SPred buildNot(SPred arg) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildNull() */
  @Override
  public SRef buildNull() {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildOr(escjava.sortedProver.NodeBuilder.SPred[]) */
  @Override
  public SPred buildOr(SPred[] args) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildPredCall(escjava.sortedProver.NodeBuilder.PredSymbol, escjava.sortedProver.NodeBuilder.SAny[]) */
  @Override
  public SPred buildPredCall(PredSymbol fn, SAny[] args) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildQVarRef(escjava.sortedProver.NodeBuilder.QuantVar) */
  @Override
  public SAny buildQVarRef(QuantVar v) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildReal(double) */
  @Override
  public SReal buildReal(double f) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue) */
  @Override
  public SValue buildSelect(SMap map, SValue idx) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildSort(escjava.sortedProver.NodeBuilder.Sort) */
  @Override
  public SAny buildSort(Sort s) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SValue) */
  @Override
  public SMap buildStore(SMap map, SValue idx, SValue val) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildTrue() */
  @Override
  public SPred buildTrue() {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildValueConversion(escjava.sortedProver.NodeBuilder.Sort, escjava.sortedProver.NodeBuilder.Sort, escjava.sortedProver.NodeBuilder.SValue) */
  @Override
  public SValue buildValueConversion(Sort from, Sort to, SValue val) {
    // TODO Implement
    assert false;
    return null;
  }

  /* @see escjava.sortedProver.NodeBuilder#buildXor(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred) */
  @Override
  public SPred buildXor(SPred arg1, SPred arg2) {
    // TODO Implement
    assert false;
    return null;
  }
}
