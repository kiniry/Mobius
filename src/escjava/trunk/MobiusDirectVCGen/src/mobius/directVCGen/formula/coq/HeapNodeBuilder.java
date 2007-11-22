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
public abstract class HeapNodeBuilder extends UnsupportedNodeBuilder {
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildNewObject(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef)
   */
  @Override
  public SPred buildNewObject(final SMap oldh, final SAny type, 
                              final SMap heap, final SValue r) {
    final CPred left = new CPred("Heap.new", new STerm[] {oldh, new CMap("p"), 
                                                          new CType("Heap.LocationObject", 
                                                                    new STerm[] {type})});
    final CPred right = new CPred("Some", 
                                  new STerm[] {new CPred(false, ",", 
                                                         new STerm[] {new CRef("loc", new STerm[] {r}), heap})});
        
    final SPred res = new CPred(false, "=", new STerm[] {left, right});
    return res;
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue)
   */
  @Override
  public SValue buildSelect(final SMap map, final SValue idx) {    
    final CRef addr = new CRef("Heap.StaticField", new STerm [] {idx});
    return new CValue("do_hget", new STerm[] {map, addr});
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SValue)
   */
  @Override
  public SMap buildStore(final SMap map, final SValue idx, final SValue val) {
    final CRef addr = new CRef("Heap.StaticField", new STerm [] {idx});
    return new CMap("Heap.update", new STerm[] {map, addr, val});
  }
  
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildDynSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny)
   */
  @Override
  public SRef buildDynLoc(final SMap heap, final SValue obj, final SAny field) {
    return new CRef("Heap.DynamicField", new STerm [] {Util.getLoc(obj), field});
  }
  
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildDynSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny)
   */
  @Override
  public SValue buildDynSelect(final SMap heap, final SValue obj, final SAny field) {
    final CRef addr = new CRef("Heap.DynamicField", new STerm [] {Util.getLoc(obj), field});
    return new CValue("do_hget", new STerm[] {heap, addr});
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildDynStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SValue)
   */
  @Override
  public SMap buildDynStore(final SMap map, final SValue obj, 
                            final SAny field, final SValue val) {
    final CRef addr = new CRef("Heap.DynamicField", new STerm [] {Util.getLoc(obj), field});
    return new CMap("Heap.update", new STerm[] {map, addr, val});
    
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildArrSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt)
   */
  @Override
  public SValue buildArrSelect(final SMap heap, final SRef obj, final SInt idx) {
    final CRef addr = new CRef("Heap.ArrayElement", new STerm [] {Util.getLoc(obj), idx});
    return new CValue("do_hget", new STerm[] {heap, addr});
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildArrStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SValue)
   */
  @Override
  public SMap buildArrStore(final SMap map, final SRef obj, final SInt idx, final SValue val) {
    final CRef addr = new CRef("Heap.ArrayElement", new STerm [] {Util.getLoc(obj), idx});
    return new CMap("Heap.update", new STerm[] {map, addr, val});
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildNewArray(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt)
   */
  @Override
  public SPred buildNewArray(final SMap oldh, final SAny type, 
                             final SMap heap, final SRef r, final SInt len) {
    final CPred left = new CPred("Heap.new", new STerm[] {oldh, new CMap("p"), 
                                                          new CType("Heap.LocationArray", 
                                                                    new STerm[] {len, type})});
    final CPred right = new CPred("Some", new STerm[] {new CPred(false, 
                                                                 ",", 
                                                          new STerm[] {new CRef("loc", new STerm[] {r}), heap})});
        
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
  
  
  @Override
  public SPred buildIsAlive(final SMap map, final SRef ref) {
    return new CPred("isAlive", new STerm [] {map, ref});
  }
}
