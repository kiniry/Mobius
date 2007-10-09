package mobius.directVCGen.formula.coq;

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
import escjava.sortedProver.EscNodeBuilder;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.SortVar;

/*@ non_null_by_default @*/
/**
 * The back-end for Coq. Works with bicolano. It does not 
 * work with ESC/Java2 right now because it uses the bicolano
 * memory model which ESC/Java2 doesn't.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CoqNodeBuilder extends EscNodeBuilder {
  
  /**
   * Normalize the symbols ... remove from the string
   * the characters Coq would not like to see
   * @param name the string to modify
   * @return the modified string
   */
  public static String normalize(final String name) {
    String resName = name;
    if (name.startsWith("#")) {
      resName = resName.substring(1);
    }
    resName = resName.replace(':', '_');
    resName = resName.replace('.', '_');
    resName = resName.replace('\\', '_');
    resName = resName.replace('?', '.');
    return resName;
  }
  
  
  /**
   * Return the symbol to get a location out of a value.
   * @param r the value to convert
   * @return a location term
   */
  public static SRef getLoc(final SValue r) {
    return new CRef("loc", new STerm[] {r});
  }
  
  
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
    else {
      res = new CType("value");
      throw new IllegalArgumentException();
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
    final String name = normalize(var.name);
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
    //return new CInt("Int.const", new STerm[]{new CInt("" + n)});
    return new CInt("" + n);
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
   * @see escjava.sortedProver.NodeBuilder#buildDistinct(escjava.sortedProver.NodeBuilder.SAny[])
   */
  @Override
  public SPred buildDistinct(final SAny[] terms) {
    throw new UnsupportedOperationException("Distinct elements don't mean anything for Coq!");
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
   * @see escjava.sortedProver.NodeBuilder#buildReal(double)
   */
  @Override
  public SReal buildReal(final double f) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildRealBoolFun(int, escjava.sortedProver.NodeBuilder.SReal, escjava.sortedProver.NodeBuilder.SReal)
   */
  @Override
  public SBool buildRealBoolFun(final int realPredTag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /*
   * (non-Javadoc)  public SPred buildIsAlive(SMap map, SRef ref) {
    throw new UnsupportedOperationException();
  }
   * @see escjava.sortedProver.NodeBuilder#buildRealFun(int, escjava.sortedProver.NodeBuilder.SReal, escjava.sortedProver.NodeBuilder.SReal)
   */
  @Override
  public SReal buildRealFun(final int realFunTag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildRealFun(int, escjava.sortedProver.NodeBuilder.SReal)
   */
  @Override
  public SReal buildRealFun(final int realFunTag, final SReal arg1) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildRealPred(int, escjava.sortedProver.NodeBuilder.SReal, escjava.sortedProver.NodeBuilder.SReal)
   */
  @Override
  public SPred buildRealPred(final int realPredTag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
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
    

    if (fn == symRefEQ) {
      return new CPred(false, "=", args);
    }
    else if (fn == symRefNE) {
      return this.buildNot(new CPred(false, "=", args));
    }
    else if (fn ==   symTypeEQ) {
      throw new IllegalArgumentException("Unimplemented symbol: " + fn);
    }
    else if (fn == symTypeNE) {
      throw new IllegalArgumentException("Unimplemented symbol: " + fn);
    }
    else if (fn == symTypeLE) {
      final SAny [] realargs = {new CMap("p"),
                                args[0], args[1]};
      return new CPred("subclass_name", realargs);
    }
    else if (fn == symAllocLT) {
      return new CPred("allocLT", args);
    }
    else if (fn == symAllocLE) {
      return new CPred("allocLE", args);
    }
    else if (fn == symLockLT) {
      return new CPred("lockLT", args);
    }
    else if (fn == symLockLE) {
      return new CPred("lockLE", args);
    }
    else if (fn == symIs) {
      throw new IllegalArgumentException("Unimplemented symbol: " + fn);
    }
    else if (fn == symCast) {
      throw new IllegalArgumentException("Unimplemented symbol: " + fn);
    }
    else if (fn == symIsAllocated) {
      return new CPred("isAllocated", args);
    }
    else {
      return new CPred(fn.name, args);
    }
    //throw new IllegalArgumentException("Unknown symbol: " + fn);
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildFnCall(escjava.sortedProver.NodeBuilder.FnSymbol, escjava.sortedProver.NodeBuilder.SAny[])
   */
  @Override
  public SAny buildFnCall(final FnSymbol fn, final SAny[] args) {
    if (fn.equals(symTypeOf)) {
      if (args.length == 2) {
        return new CType("typeof", args[0], getLoc((SValue)args[1]));
      }
    }
    throw new IllegalArgumentException("Unknown symbol: " + fn);
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildLabel(boolean, java.lang.String, escjava.sortedProver.NodeBuilder.SPred)
   */
  @Override
  public SPred buildLabel(final boolean positive, final String name, final SPred pred) {
    throw new UnsupportedOperationException("Labels have no real meanings for us, right?");
  }
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildValueConversion(escjava.sortedProver.NodeBuilder.Sort, escjava.sortedProver.NodeBuilder.Sort, escjava.sortedProver.NodeBuilder.SValue)
   */
  @Override
  public SValue buildValueConversion(final Sort from, final Sort to, final SValue val) {
    if (from == sortValue) {
      if (to == sortRef) {
        return val;
      }
      else if (to == sortBool) {
        return new CBool("vBool", new STerm[] {val});
      }
      else if (to == sortInt) {
        return new CInt("vInt", new STerm[] {val});
      }
      else if (to == sortReal) {
        throw new UnsupportedOperationException("We do not support reals right now...");
      }
      else {
        throw new IllegalArgumentException("The conversion can only be done " +
            "from a value to a simple type. Found:" + to);
      }
    }
    else {
      if (to != sortValue) {
        throw new IllegalArgumentException("The conversion can only be done " +
            "from a simple type to a value. Found:" + to);
      }
      if (from == sortRef) {
        return val;
      }
      else if (from == sortBool) {
        return new CValue("Num", new CInt("B ", new STerm[] {val}));
      }
      else if (from == sortInt) {
        return new CValue("Num", new CInt("I ", new STerm[] {val}));
      }
      else if (from == sortReal) {
        throw new UnsupportedOperationException("We do not support reals right now...");
      }
      else {
        throw new IllegalArgumentException("The conversion can only be done from a value " +
            "to a simple type. Found:" + to);
      }
      
    }
  }

  

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildNewObject(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef)
   */
  @Override
  public SPred buildNewObject(final SMap oldh, final SAny type, 
                              final SMap heap, final SRef r) {
    final CPred left = new CPred("Heap.new", new STerm[] {oldh, new CMap("p"), 
                                                          new CType("Heap.LocationObject", 
                                                                    new STerm[] {type})});
    final CPred right = new CPred("Some", 
                                  new STerm[] {new CPred(false, ",", 
                                                         new STerm[] {getLoc(r), heap})});
        
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
    return new CValue("get", new STerm[] {map, addr});
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
  //TODO: cbr: change body of this method. copied out of buildDynSelect
  public SRef buildDynLoc(final SMap heap, final SRef obj, final SRef field) {
    final CRef addr = new CRef("Heap.DynamicField", new STerm [] {getLoc(obj), field});
    return new CRef("get", new STerm[] {heap, addr});
  }
  
  
  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildDynSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny)
   */
  @Override
  public SValue buildDynSelect(final SMap heap, final SRef obj, final SAny field) {
    final CRef addr = new CRef("Heap.DynamicField", new STerm [] {getLoc(obj), field});
    return new CValue("get", new STerm[] {heap, addr});
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildDynStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SValue)
   */
  @Override
  public SMap buildDynStore(final SMap map, final SRef obj, 
                            final SAny field, final SValue val) {
    final CRef addr = new CRef("Heap.DynamicField", new STerm [] {getLoc(obj), field});
    return new CMap("Heap.update", new STerm[] {map, addr, val});
    
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildArrSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt)
   */
  @Override
  public SValue buildArrSelect(final SMap heap, final SRef obj, final SInt idx) {
    final CRef addr = new CRef("Heap.ArrayElement", new STerm [] {getLoc(obj), idx});
    return new CValue("get", new STerm[] {heap, addr});
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildArrStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SValue)
   */
  @Override
  public SMap buildArrStore(final SMap map, final SRef obj, final SInt idx, final SValue val) {
    final CRef addr = new CRef("Heap.ArrayElement", new STerm [] {getLoc(obj), idx});
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
                                                          new STerm[] {getLoc(r), heap})});
        
    final SPred res = new CPred(false, "=", new STerm[] {left, right});
    return res;
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildConstantRef(escjava.sortedProver.NodeBuilder.FnSymbol)
   */
  @Override
  public SAny buildConstantRef(final FnSymbol c) {
    throw new UnsupportedOperationException();
  }

  /*
   * (non-Javadoc)
   * @see escjava.sortedProver.NodeBuilder#buildIff(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred)
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
        res = new CInt(false, "+", new STerm[] {arg1, arg2});
        break;
      case NodeBuilder.funSUB:
        res = new CInt(false, "-", new STerm[] {arg1, arg2});
        break;
      case NodeBuilder.funMUL:
        res = new CInt(false, "*", new STerm[] {arg1, arg2});
        break;
      case NodeBuilder.funDIV:
        res = new CInt(false, "/", new STerm[] {arg1, arg2});
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
   * @see escjava.sortedProver.NodeBuilder#buildIntFun(int, escjava.sortedProver.NodeBuilder.SInt)
   */
  @Override
  public SInt buildIntFun(final int intFunTag, final SInt arg1) {
    throw new UnsupportedOperationException();
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
   * @see escjava.sortedProver.NodeBuilder#buildXor(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred)
   */
  @Override
  public SPred buildXor(final SPred arg1, final SPred arg2) {
    throw new UnsupportedOperationException();
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
  
  
  
  public SPred buildIsFieldOf(SMap map, SRef obj, SAny field) {
    return new CPred("isFieldOf", new STerm [] {map, obj, field});
  }
  


  @Override
  public SBool buildRefBoolFun(int refPredTag, SRef arg1, SRef arg2) {
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
