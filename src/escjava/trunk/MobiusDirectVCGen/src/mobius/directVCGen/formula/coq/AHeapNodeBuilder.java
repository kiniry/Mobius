package mobius.directVCGen.formula.coq;

import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.coq.representation.CMap;
import mobius.directVCGen.formula.coq.representation.CPred;
import mobius.directVCGen.formula.coq.representation.CRef;
import mobius.directVCGen.formula.coq.representation.CType;
import mobius.directVCGen.formula.coq.representation.CValue;

/**
 * This class builds Heap related nodes.
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class AHeapNodeBuilder extends AUnsupportedNodeBuilder {
  /** {@inheritDoc} */
  @Override
  public SPred buildNewObject(final SMap oldh, final SAny type, 
                              final SMap heap, final SValue r) {
    final CPred left = new CPred("Heap.new", new STerm[] {oldh, new CMap("p"), 
                                                          new CType("Heap.LocationObject", 
                                                                    new STerm[] {type})});
    final CPred right = new CPred("Some", CPred.mkCouple(new CRef("loc", r), heap));
        
    final SPred res = new CPred(false, "=", left, right);
    return res;
  }
  
  /** {@inheritDoc} */
  @Override
  public SValue buildSelect(final SMap map, final SValue idx) {    
    final CRef addr = new CRef("Heap.StaticField", idx);
    return new CValue("do_hget", new STerm[] {map, addr});
  }
  
  /** {@inheritDoc} */
  @Override
  public SMap buildStore(final SMap map, final SValue idx, final SValue val) {
    final CRef addr = new CRef("Heap.StaticField", idx);
    return new CMap("Heap.update", new STerm[] {map, addr, val});
  }
  
  /** {@inheritDoc} */
  @Override
  public SRef buildDynLoc(final SMap heap, final SValue obj, final SAny field) {
    return new CRef("Heap.DynamicField", new STerm [] {Util.getLoc(obj), field});
  }
  
  
  /** {@inheritDoc} */
  @Override
  public SValue buildDynSelect(final SMap heap, final SValue obj, final SAny field) {
    final CRef addr = new CRef("Heap.DynamicField", new STerm [] {Util.getLoc(obj), field});
    return new CValue("do_hget", new STerm[] {heap, addr});
  }

  /** {@inheritDoc} */
  @Override
  public SMap buildDynStore(final SMap map, final SValue obj, 
                            final SAny field, final SValue val) {
    final CRef addr = new CRef("Heap.DynamicField", new STerm [] {Util.getLoc(obj), field});
    return new CMap("Heap.update", new STerm[] {map, addr, val});
    
  }

  /** {@inheritDoc} */
  @Override
  public SValue buildArrSelect(final SMap heap, final SRef obj, final SInt idx) {
    final CRef addr = new CRef("Heap.ArrayElement", new STerm [] {Util.getLoc(obj), idx});
    return new CValue("do_hget", new STerm[] {heap, addr});
  }

  /** {@inheritDoc} */
  @Override
  public SMap buildArrStore(final SMap map, final SRef obj, final SInt idx, final SValue val) {
    final CRef addr = new CRef("Heap.ArrayElement", new STerm [] {Util.getLoc(obj), idx});
    return new CMap("Heap.update", new STerm[] {map, addr, val});
  }

  /** {@inheritDoc} */
  @Override
  public SPred buildNewArray(final SMap oldh, final SAny type, 
                             final SMap heap, final SRef r, final SInt len) {
    final CPred left = new CPred("Heap.new", new STerm[] {oldh, new CMap("p"), 
                                                          new CType("Heap.LocationArray", 
                                                                    new STerm[] {len, type})});
    final CPred right = new CPred("Some", CPred.mkCouple(new CRef("loc", r), heap));
        
    final SPred res = new CPred(false, "=", new STerm[] {left, right});
    return res;
  }
  
  /**
   * Should generate something of the form:
   * \forall x,t : isAlive(heap, x) & typeof(x)=t -> inv(heap, x, t) .
   * @param map the actual heap
   * @param val the ref add infos upon
   * @param type the type associated to the reference
   * @return a Coq term ready to be printed
   */
  @Override
  public SPred buildInv(final SMap map, final SValue val, final SAny type) {
    return new CPred("inv", new STerm [] {map, val, type});
  }
  
  /** {@inheritDoc} */
  @Override
  public SPred buildIsAlive(final SMap map, final SRef ref) {
    return new CPred("isAlive", new STerm [] {map, ref});
  }
}
