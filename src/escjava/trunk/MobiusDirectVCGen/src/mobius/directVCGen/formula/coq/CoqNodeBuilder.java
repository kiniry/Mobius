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
public class CoqNodeBuilder extends HeapNodeBuilder {
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildSort(escjava.sortedProver.NodeBuilder.Sort)
   */
  @Override
  public SAny buildSort(final Sort type) {
    SAny res;
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
      //throw new IllegalArgumentException();
    }
    return res;
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildAnd(escjava.sortedProver.NodeBuilder.SPred[])
   */
  @Override
  public SPred buildAnd(final SPred[] args) {
    return new CPred(false, "/\\", args);
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildAnyEQ(escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SAny)
   */
  @Override
  public SPred buildAnyEQ(final SAny arg1, final SAny arg2) {
    return new CPred(false, "=", new STerm[] {arg1, arg2});
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildAnyNE(escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SAny)
   */
  @Override
  public SPred buildAnyNE(final SAny arg1, final SAny arg2) {
    return new CPred(false, "not", new STerm[] {buildAnyEQ(arg1, arg2)});
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildBool(boolean)
   */
  @Override
  public SBool buildBool(final boolean b) {
    return new CBool(b ? "true" : "false");
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildImplies(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred)
   */
  @Override
  public SPred buildImplies(final SPred arg1, final SPred arg2) {
    return new CPred(false, "->", new STerm [] {arg1, arg2});
  }
  
  @Override
  public SPred buildForAll(final QuantVar[] vars, final SPred body, 
                           final STerm[][] pats, final STerm[] nopats) {
    return new CForall(this, vars, body);
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildQVarRef(escjava.sortedProver.NodeBuilder.QuantVar)
   */
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



  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildInt(long)
   */
  @Override
  public SInt buildInt(final long n) {
    return new CInt("Int.const", new STerm[]{new CInt("(" + n + ")")});
    //return new CInt("Int.const " + n);
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildIntBoolFun(int, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SInt)
   */
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
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildIsTrue(escjava.sortedProver.NodeBuilder.SBool)
   */
  @Override
  public SPred buildIsTrue(final SBool val) {
    return new CPred("Is_true", new STerm[] {val});
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildExists(escjava.sortedProver.NodeBuilder.QuantVar[], escjava.sortedProver.NodeBuilder.SPred)
   */
  @Override
  public SPred buildExists(final QuantVar[] vars, final SPred body) {
    if (vars.length == 0) {
      return body;
    }
    return new CExists(this, vars, body);
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildNull()
   */
  @Override
  public SRef buildNull() {
    return new CRef("Null");
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildITE(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SValue)
   */
  @Override
  public SValue buildITE(final SPred cond, final SValue thenPart, final SValue elsePart) {
    // should not appear in this form ... the typing is a bit loosy
    throw new UnsupportedOperationException("I don't like this construct, get rid of it!");
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildNot(escjava.sortedProver.NodeBuilder.SPred)
   */
  @Override
  public SPred buildNot(final SPred arg) {
    return new CPred("not", new STerm[] {arg});
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildTrue()
   */
  @Override
  public SPred buildTrue() {
    return new CPred("True");
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildOr(escjava.sortedProver.NodeBuilder.SPred[])
   */
  @Override
  public SPred buildOr(final SPred[] args) {
    return new CPred(false, "\\/", args);
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildPredCall(escjava.sortedProver.NodeBuilder.PredSymbol, escjava.sortedProver.NodeBuilder.SAny[])
   */
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
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildFnCall(escjava.sortedProver.NodeBuilder.FnSymbol, escjava.sortedProver.NodeBuilder.SAny[])
   */
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


  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildValueConversion(escjava.sortedProver.NodeBuilder.Sort, escjava.sortedProver.NodeBuilder.Sort, escjava.sortedProver.NodeBuilder.SValue)
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

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildIntFun(int, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SInt)
   */
  @Override
  public SInt buildIntFun(final int intFunTag, final SInt arg1, final SInt arg2) {
    SInt res;
    switch (intFunTag) {
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
                                                NodeBuilder.tagsIds[intFunTag]);
    }
    return res;

  }


  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildIntPred(int, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SInt)
   */
  @Override
  public SPred buildIntPred(final int intPredTag, final SInt arg1, final SInt arg2) {
    CPred res;
    switch (intPredTag) {
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
        throw new UnsupportedOperationException(NodeBuilder.tagsIds[intPredTag]);
    }
    return res;
  }



  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildAssignCompat(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SAny)
   */
  @Override
  public SPred buildAssignCompat(final SMap map, final SValue val, final SAny type) {
    String typeStmt = type.toString();
    if (typeStmt.startsWith("T_")) {
      typeStmt = typeStmt.substring(2);
      
      
    }
    return new CPred("assign_compatible", new STerm [] {new CMap("p"), map, val, type});
  }



  
  
  
  public SPred buildAssignPred(final SMap map, final SMap preMap, 
                               final SRef target, final SRef loc) {
    return new CPred("assignPred", new STerm [] {map, preMap, target, loc});
  }
  


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
