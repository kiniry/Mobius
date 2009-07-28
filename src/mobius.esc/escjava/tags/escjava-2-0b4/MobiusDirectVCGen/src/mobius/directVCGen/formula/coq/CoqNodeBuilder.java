package mobius.directVCGen.formula.coq;

import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.coq.representation.CBool;
import mobius.directVCGen.formula.coq.representation.CExists;
import mobius.directVCGen.formula.coq.representation.CForall;
import mobius.directVCGen.formula.coq.representation.CInt;
import mobius.directVCGen.formula.coq.representation.CMap;
import mobius.directVCGen.formula.coq.representation.CPred;
import mobius.directVCGen.formula.coq.representation.CReal;
import mobius.directVCGen.formula.coq.representation.CRef;
import mobius.directVCGen.formula.coq.representation.CType;
import mobius.directVCGen.formula.coq.representation.CValue;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.SortVar;

/*@ non_null_by_default @*/
/**
 * The back-end for Coq. Works with bicolano. It does not 
 * work with ESC/Java2 right now because it uses the bicolano
 * memory model which ESC/Java2 doesn't.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CoqNodeBuilder extends AHeapNodeBuilder {

  /**
   * Build the Coq representation of a sort.
   * @param type the type to convert
   * @return the coq term representing the sort,
   * of type CType.
   */
  @Override
  public SAny buildSort(final Sort type) {
    CType res;
    Sort realtype;
    if (type instanceof SortVar) {
      realtype = type.theRealThing();
    }
    else {
      realtype = type;
    }
    
    if (realtype.equals(sortPred)) {
      res =  new CType("Prop");
    }
    else if (realtype.equals(sortInt)) {
      res =  new CType("Int.t");
    }
    else if (realtype.equals(sortReal)) {
      res = new CType("Real");
    }
    else if (realtype.equals(sortRef)) {
      res = new CType("value");
    }
    else if (realtype.equals(sortBool)) {
      res = new CType("bool");
    }
    else if (realtype.equals(sortMap)) {
      res = new CType("Heap.t");
    }
    else if (realtype.equals(sortType)) {
      res = new CType("type");
    }
    else if (realtype.equals(sortField)) {
      res = new CType("FieldSignature");
    }
    else {
      res = new CType("value");
    }
    return res;
  }
  
  /** {@inheritDoc} */
  @Override
  public SPred buildAnd(final SPred[] args) {
    return new CPred(false, "/\\", args);
  }

  /** {@inheritDoc} */
  @Override
  public SPred buildAnyEQ(final SAny arg1, final SAny arg2) {
    return new CPred(false, "=", new STerm[] {arg1, arg2});
  }

  /** {@inheritDoc} */
  @Override
  public SPred buildAnyNE(final SAny arg1, final SAny arg2) {
    return new CPred(false, "not", new STerm[] {buildAnyEQ(arg1, arg2)});
  }


  /** {@inheritDoc} */
  @Override
  public SBool buildBool(final boolean b) {
    return new CBool(b ? "true" : "false");
  }

  /** {@inheritDoc} */
  @Override
  public SPred buildImplies(final SPred arg1, final SPred arg2) {
    return new CPred(false, "->", new STerm [] {arg1, arg2});
  }
  
  /** {@inheritDoc} */
  @Override
  public SPred buildForAll(final QuantVar[] vars, final SPred body, 
                           final STerm[][] pats, final STerm[] nopats) {
    return new CForall(this, vars, body);
  }
  

  /** {@inheritDoc} */
  @Override
  public SAny buildQVarRef(final QuantVar var) {
    final String name = Util.normalize(var.name);
    Sort s = var.type;
    if (s instanceof SortVar) {
      s = s.theRealThing();
    }
    
    SAny res;
    if (s.equals(sortBool)) {
      res = new CBool(name);
    }
    else if (s.equals(sortRef)) {
      res = new CRef(name);
    }
    else if (s.equals(sortInt)) {
      res = new CInt(name);
    }
    else if (s.equals(sortReal)) {
      res = new CReal(name);
    }
    else if (s.equals(sortMap)) {
      res = new CMap(name);
    }
    else if (s.equals(sortType)) {
      res = new CType(name);
    }
    else if (s.equals(sortField)) {
      res = new CRef(name);
    }
    else if (s.equals(sortValue)) {
      res = new CValue(name);
    }
    else if (s.equals(sortAny)) {
      res = new CRef(name);
      throw new IllegalArgumentException("The type of " + var + 
                                         " should not be any, it should be known!");
    }
    else if (s.equals(sortPred)) {
      throw new IllegalArgumentException("The type should not be pred!");
    }
    else {
      throw new IllegalArgumentException("Unknown Type: " + s.getClass() + 
                                    " " + sortRef.getClass());
    }
    return res;
  }



  /** {@inheritDoc} */
  @Override
  public SInt buildInt(final long n) {
    return new CInt("Int.const", new STerm[]{new CInt("(" + n + ")")});
    //return new CInt("Int.const " + n);
  }

  /** {@inheritDoc} */
  @Override
  public SBool buildIntBoolFun(final int tag, final SInt arg1, final SInt arg2) {
    switch (tag) {
      case predEQ:
        return new CBool("eq_bool", new STerm[]{arg1, arg2});
      case predLT:
        return new CBool("lt_bool", new STerm[]{arg1, arg2});
      case predLE:
        return new CBool("le_bool", new STerm[]{arg1, arg2});

      case predGT:  
      case predGE:
        throw new UnsupportedOperationException("Constructs gt or ge should" + 
                                                " be desugared to lt and le...");
      default:
        throw new IllegalArgumentException("Unknown tag " + tag);
        
    }
  }
  

  /** {@inheritDoc} */
  @Override
  public SPred buildIsTrue(final SBool val) {
    return new CPred("Is_true", new STerm[] {val});
  }
  

  /** {@inheritDoc} */
  @Override
  public SPred buildExists(final QuantVar[] vars, final SPred body) {
    if (vars.length == 0) {
      return body;
    }
    return new CExists(this, vars, body);
  }

  /** {@inheritDoc} */
  @Override
  public SRef buildNull() {
    return new CRef("Null");
  }
  
  /** {@inheritDoc} */
  @Override
  public SValue buildITE(final SPred cond, final SValue thenPart, final SValue elsePart) {
    // should not appear in this form ... the typing is a bit loosy
    throw new UnsupportedOperationException("I don't like this construct, get rid of it!");
  }
  
  /** {@inheritDoc} */
  @Override
  public SPred buildNot(final SPred arg) {
    return new CPred("not", new STerm[] {arg});
  }
  
  /**
   * Build a node representing <code>True</code>.
   * @return the predicate <code>True</code>
   */
  @Override
  public SPred buildTrue() {
    return new CPred("True");
  }
  

  /** {@inheritDoc} */
  @Override
  public SPred buildOr(final SPred[] args) {
    return new CPred(false, "\\/", args);
  }
  
  /** {@inheritDoc} */
  @Override
  public SPred buildPredCall(final PredSymbol fn, final SAny[] args) {
    

    SPred pred = null;
    if ((fn == symIs) || (fn == symCast) || 
        (fn == symTypeNE) || (fn == symTypeEQ)) {
      throw new IllegalArgumentException("Unimplemented symbol: " + fn);
    }
    else if (fn == symRefEQ) {
      pred = new CPred(false, "=", args);
    }
    else if (fn == symRefNE) {
      pred = buildNot(new CPred(false, "=", args));
    }
    else if (fn == symTypeLE) {
      final SAny [] realargs = {new CMap("p"),
                                args[0], args[1]};
      pred = new CPred("subclass_name", realargs);
    }
    else if (fn == symAllocLT) {
      pred = new CPred("allocLT", args);
    }
    else if (fn == symAllocLE) {
      pred = new CPred("allocLE", args);
    }
    else if (fn == symLockLT) {
      pred = new CPred("lockLT", args);
    }
    else if (fn == symLockLE) {
      pred = new CPred("lockLE", args);
    }
    else if (fn == symIsAllocated) {
      pred = new CPred("isAllocated", args);
    }
    else  { // yippie!!! it's a predicate!
      pred = new CPred(fn.name, args);
    }
    return pred;
  }
  
  /** {@inheritDoc} */
  @Override
  public SAny buildFnCall(final FnSymbol fn, final SAny[] args) {
    SAny res = null;
    if (fn.equals(symTypeOf) && (args.length == 2)) {
      res = new CType("typeof", args[0], Util.getLoc((SValue)args[1]));
    }
    if (fn.name.startsWith("(PrimitiveType")) {
      res = new CType(fn.name);
    }
    if (fn.name.startsWith("do_lvget")) {
      res = new CValue(fn.name, args);
    }
    if (fn.name.startsWith("LocalVar.update")) {
      res = new CRef(fn.name, args);
    }
    else {
      throw new IllegalArgumentException("Unknown symbol: " + fn);
    }
    return res;
  }


  /**
   * Add the conversion function to a given term.
   * It converts from a sort to another sort. One of the sort
   * has to be a value.
   * @param from the sort to convert from
   * @param to the sort to convert to
   * @param val the term to convert
   * @return the new converted term
   */
  @Override
  public SValue buildValueConversion(final Sort from, final Sort to, final SValue val) {
    if (from == sortValue) {
      return convertFromValue(to, val);
    }
    else {
      if (to != sortValue) {
        throw new IllegalArgumentException("The conversion can only be done " +
            "from a simple type to a value. Found:" + to);
      }
      return convertToValue(from, val);
      
    }
  }

  /**
   * Convert a term from a given sort to a value. 
   * @param from the sort to convert from
   * @param term the term to convert
   * @return a converted term
   */
  private SValue convertToValue(final Sort from, final SValue term) {
    if (from == sortRef) {
      return term;
    }
    else if (from == sortBool) {
      return new CValue("Num", new CInt("B ", new STerm[] {term}));
    }
    else if (from == sortInt) {
      return new CValue("Num", new CInt("I ", new STerm[] {term}));
    }
    else if (from == sortReal) {
      throw new UnsupportedOperationException("We do not support reals right now...");
    }
    else {
      throw new IllegalArgumentException("The conversion can only be done from a value " +
          "to a simple type. Found:" + from);
    }
  }

  /**
   * Convert a term from a value to a given sort.
   * @param to the sort to convert to
   * @param term the term to convert
   * @return a converted term
   */
  private SValue convertFromValue(final Sort to, final SValue term) {
    if (to == sortRef) {
      return term;
    }
    else if (to == sortBool) {
      return new CBool("vBool", new STerm[] {term});
    }
    else if (to == sortInt) {
      return term; //new CInt("vInt", new STerm[] {val});
    }
    else if (to == sortReal) {
      throw new UnsupportedOperationException("We do not support reals right now...");
    }
    else {
      throw new IllegalArgumentException("The conversion can only be done " +
          "from a value to a simple type. Found:" + to);
    }
  }


  /**
   * Build an equivalence expression: <code>&lt;-></code>.
   * @param arg1 the left part
   * @param arg2 the right part
   * @return the equivalence expression
   */
  @Override
  public SPred buildIff(final SPred arg1, final SPred arg2) {
    return new CPred(false, "<->", new STerm [] {arg1, arg2});
  }

  /** {@inheritDoc} */
  @Override
  public SInt buildIntFun(final int tag, final SInt arg1, final SInt arg2) {
    SInt res;
    switch (tag) {
      case NodeBuilder.funADD:
        res = new CInt("Int.add", new STerm[] {arg1, arg2});
        break;
      case NodeBuilder.funSUB:
        res = new CInt("Int.sub", new STerm[] {arg1, arg2});
        break;
      case NodeBuilder.funMUL:
        res = new CInt("Int.mul", new STerm[] {arg1, arg2});
        break;
      case NodeBuilder.funDIV:
        res = new CInt("Int.div", new STerm[] {arg1, arg2});
        break;
      case NodeBuilder.funMOD:
        res = new CInt("Int.mod", new STerm[] {arg1, arg2});
        break;
      default:
        throw new UnsupportedOperationException("Cannot translate the tag: " + 
                                                NodeBuilder.tagsIds[tag]);
    }
    return res;

  }


  /** {@inheritDoc} */
  @Override
  public SPred buildIntPred(final int tag, final SInt arg1, final SInt arg2) {
    CPred res;
    switch (tag) {
      case NodeBuilder.predLE:
        res = new CPred(false, "<=", arg1,
                      arg2);
        break;
      case NodeBuilder.predLT:
        res = new CPred(false, "<", arg1,
            arg2);
        break;
      case NodeBuilder.predGT:
        res = new CPred(false, "<=", arg2,
            arg1);
        break;
      case NodeBuilder.predGE:
        res = new CPred(false, "<", arg2,
                      arg1);
        break;
      case NodeBuilder.predEQ:
        res = new CPred(false, "=", arg1,
            arg2);
        break;
      default:
        throw new UnsupportedOperationException(NodeBuilder.tagsIds[tag]);
    }
    return res;
  }



  /** {@inheritDoc} */
  @Override
  public SPred buildAssignCompat(final SMap map, final SValue val, final SAny type) {
    String typeStmt = type.toString();
    if (typeStmt.startsWith("T_")) {
      typeStmt = typeStmt.substring(2); 
    }
    return new CPred("assign_compatible", new STerm [] {new CMap("p"), map, val, type});
  }



  
  /** {@inheritDoc} */
  @Override
  public SPred buildAssignPred(final SMap map, final SMap preMap, 
                               final SRef target, final SRef loc) {
    return new CPred("assignPred", new STerm [] {map, preMap, target, loc});
  }
  

  /** {@inheritDoc} */
  @Override
  public SBool buildRefBoolFun(final int refPredTag, 
                               final SRef arg1, 
                               final SRef arg2) {
    String sym;
    switch (refPredTag) {
      case NodeBuilder.predEQ:
        sym = "refeq";
        break;
      case NodeBuilder.predNE:
      default:
        sym = "refneq";
        break; 
    }
    
    return new CBool(false, sym, new STerm[] {arg1, arg2});
  }


}
