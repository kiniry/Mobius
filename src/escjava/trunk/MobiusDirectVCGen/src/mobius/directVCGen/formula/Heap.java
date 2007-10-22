package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * This library contains most of the methods to do heap manipulation / 
 * heap access <i>etc.</i>. It notably contains the heap variable.
 * @author J. Charles (julien.charles@inria.fr), H. Lehner
 */
public final class Heap {
  /** the sort that represents the type of a heap. */
  public  static final Sort sort = Formula.lf.sortMap;
  public  static final Sort sortValue = Formula.lf.sortValue;
  /** the variable representing the heap. */
  public static final QuantVariableRef var = Expression.rvar("heap", sort);

  /** the variable used for the local variables. */
  private static final QuantVariableRef lvvar = Expression.rvar("lv", Ref.sort);

  public static final QuantVariableRef lvvarPre = Expression.old(lvvar);

  /** the variable representing the heap in the prestate. */
  public static final QuantVariableRef varPre = Expression.old(var);

  /** the counter to count the number of instanciation of the heap variable. */
  private static int heapc;
  private static int lvc;
  
  /**
   * @deprecated
   */
  private Heap() {
    
  }
  
  /**
   * Creates a formula that represents a store upon a static variable.
   * @param heap the current heap
   * @param var the static field where to do the store
   * @param val the value to store
   * @return the new heap, after the store 
   */
  public static Term store(final QuantVariableRef heap, final QuantVariable var,
                           final  Term val) {
    return Formula.lf.mkFnTerm(Formula.lf.symStore, 
                               new Term[] {heap, Expression.rvar(var), sortToValue(val)});
  }

  /**
   * Creates a formula that represents a store upon an instance field.
   * @param heap the heap on which to do the store
   * @param obj the instance object to which belong the field
   * @param var the name of the field to store
   * @param val the value to store in the field
   * @return a newly formed heap, after the store
   */
  public static Term store(final QuantVariableRef heap, final Term obj, 
                           final QuantVariable var, final Term val) {
    return Formula.lf.mkFnTerm(Formula.lf.symDynStore, 
                               new Term[] {heap, obj, Expression.rvar(var), sortToValue(val)});
  }


  /**
   * Creates a formula that represents a store to an array.
   * @param heap the current heap
   * @param var the variable that represents the array
   * @param idx the index to which to store the value
   * @param val the value to store
   * @return the newly formed heap
   */
  public static Term storeArray(final QuantVariableRef heap, final Term var, 
                                final Term idx, final Term val) {
    if (!heap.getSort().equals(Heap.sort)) {
      throw new IllegalArgumentException("The heap argument should be of sort heap, found: " + 
                                         heap.getSort());
    }
    if (!var.getSort().equals(Ref.sort)) {
      throw new IllegalArgumentException("The var argument should be of sort reference, " +
          "found: " + var.getSort());
    }

    if (!idx.getSort().equals(Num.sortInt)) {
      throw new IllegalArgumentException("The idx argument should be of sort int, found: " + 
                                         idx.getSort());
    }
    return Formula.lf.mkFnTerm(Formula.lf.symArrStore, new Term[] {heap,  var, 
                                                                   idx, 
                                                                   sortToValue(val)});
  }

  /**
   * The select for a static field.
   * @param heap the heap on which to do the select
   * @param var the name of the field to select
   * @return the term representing the select
   */
  public static Term select(final QuantVariableRef heap, final QuantVariable var) {
    final Term select = Formula.lf.mkFnTerm(Formula.lf.symSelect, 
                                      new Term[] {heap, Expression.rvar(var)});
    return valueToSort(select, var.type);
  }

  /**
   * The select for a dynamic field.
   * @param heap the heap on which to do the select
   * @param obj the object to which the field belong
   * @param var the name of the field on which to do the select
   * @param type the type of the result of the select
   * @return the term representing the select
   */
  public static Term select(final QuantVariableRef heap, final Term obj, 
                            final QuantVariable var, Sort type) {
    final Term select = Formula.lf.mkFnTerm(Formula.lf.symDynSelect, 
                                      new Term[] {heap, obj, Expression.rvar(var)});
    return valueToSort(select, type);
  }
  
  
  /**
   * The location (loc) for a dynamic field.
   * @param heap the heap on which to do the loc
   * @param obj the object to which the field belong
   * @param var the name of the field on which to do the loc
   * @return the term representing the loc
   */
  public static Term loc(final QuantVariableRef heap, final Term obj, 
                            final QuantVariable var) {
    final Term loc = Formula.lf.mkFnTerm(Formula.lf.symDynLoc, 
                                      new Term[] {heap, obj, Expression.rvar(var)});
    //return valueToSort(loc, var.type);
    return loc;
  }
  

  /**
   * The select for an element of an array.
   * @param heap the heap on which to do the select
   * @param var the array
   * @param idx the index of the element to retrieve
   * @param type the type of the element to retrieve
   * @return the construct well instanciated
   */
  public static Term selectArray(final Term heap, final Term var, 
                                 final Term idx, final Sort type) {
    if (!heap.getSort().equals(Heap.sort)) {
      throw new IllegalArgumentException("The heap argument should be of sort heap, found: " + 
                                         heap.getSort());
    }
    if (!var.getSort().equals(Ref.sort)) {
      throw new IllegalArgumentException("The var argument should be of sort reference, " +
          "found: " + var.getSort());
    }

    if (!idx.getSort().equals(Num.sortInt)) {
      throw new IllegalArgumentException("The idx argument should be of sort int, found: " + 
                                         idx.getSort());
    }
    final Term select = Formula.lf.mkFnTerm(Formula.lf.symArrSelect, 
                                            new Term[] {heap, var, idx});
    return valueToSort(select, type);
  }


  /**
   * Create a term that is a conversion from the value to the specified 
   * sort.
   * @param t the term to convert
   * @param type the type to which to convert the term
   * @return the conversion term
   */
  public static Term valueToSort(final Term t, final Sort type) {
    FnTerm res;
    if (type == Formula.lf.sortBool) {
      res = Formula.lf.mkFnTerm(Formula.lf.symValueToBool,  new Term [] {t});
    }
    else if (type == Formula.lf.sortRef) {
      res = Formula.lf.mkFnTerm(Formula.lf.symValueToRef,  new Term [] {t});
    }
    else if (type == Formula.lf.sortInt) {
      res = Formula.lf.mkFnTerm(Formula.lf.symValueToInt,  new Term [] {t});
    }
    else if (type == Formula.lf.sortReal) {
      res = Formula.lf.mkFnTerm(Formula.lf.symValueToReal,  new Term [] {t});
    }
    else if (type == Formula.lf.sortAny) {
      res = Formula.lf.mkFnTerm(Formula.lf.symValueToAny,  new Term [] {t});
    }
    else {
      throw new IllegalArgumentException("Bad type " +
                                         "found: " + type);
    }
    return res;
  }

  /**
   * It cast a variable of any sort to a value.
   * @param t the variable to convert to a value
   * @return the converted variable
   */
  public static Term sortToValue(final Term t) {
    Sort s = t.getSort();
    s = s.theRealThing();
    FnTerm res;
    if (s.equals(Formula.lf.sortBool)) {
      res = Formula.lf.mkFnTerm(Formula.lf.symBoolToValue,  new Term [] {t});
    }
    else if (s.equals(Formula.lf.sortRef)) {
      res = Formula.lf.mkFnTerm(Formula.lf.symRefToValue,  new Term [] {t});
    }
    else if (s.equals(Formula.lf.sortInt)) {
      res = Formula.lf.mkFnTerm(Formula.lf.symIntToValue,  new Term [] {t});
    }
    else if (s.equals(Formula.lf.sortReal)) {
      res = Formula.lf.mkFnTerm(Formula.lf.symRealToValue,  new Term [] {t});
    }
    else {
      throw new IllegalArgumentException("Bad type " +
                                         "found for " + t.getClass() + " " + 
                                         t + ": " + t.getSort());
    }
    return res;
  }



  /**
   * Creates and return a new instance of the heap variable.
   * @return a new heap variable
   */
  public static QuantVariableRef newVar() {
    return Expression.rvar("heap" + (heapc++), Heap.sort);
  }
  public static QuantVariableRef newLvVar() {
    return Expression.rvar("lv" + (lvc++), Ref.sort);
  }
  /**
   * Create the term to represent creation of a new object.
   * It takes the old heap, the type of the location to allocate
   * the new heap and the new location to allocate
   * @param oldheap the old heap
   * @param type the type of the newly allocated thing
   * @param heap the new heap
   * @param e the location that has been allocated, represented by a variable
   * @return a predicate representing the creation of a new object
   */
  public static Term newObject(final Term oldheap, final Term type, 
                               final Term heap,  final QuantVariableRef e) {
    if (!oldheap.getSort().equals(Heap.sort)) {
      throw new IllegalArgumentException("The old heap must be of type heap! Found: " + 
                                         oldheap.getSort());
    }
    if (!heap.getSort().equals(Heap.sort)) {
      throw new IllegalArgumentException("The new heap must be of type heap! Found: " + 
                                         heap.getSort());
    }
    if (!type.getSort().equals(Type.sort)) {
      throw new IllegalArgumentException("The type must be of type type! Found: " + 
                                         type.getSort());
    }

    return Formula.lf.mkFnTerm(Formula.lf.symNewObj, new Term[] {oldheap, type, heap, e});
  }

  /**
   * Create the term representing the creation of an array.
   * @param oldheap the heap before the creation
   * @param type the type of the array elements
   * @param heap the new heap after the array creation
   * @param dim the dimension of the array
   * @param loc the new location to allocate
   * @return the predicate representing the creation of an array
   */
  public static Term newArray(final QuantVariableRef oldheap,  final Term type, 
                              final QuantVariableRef heap, final Term dim, 
                              final QuantVariableRef loc) {
    if (!oldheap.getSort().equals(Heap.sort)) {
      throw new IllegalArgumentException("The old heap must be of type heap! Found: " + 
                                         oldheap.getSort());
    }
    if (!heap.getSort().equals(Heap.sort)) {
      throw new IllegalArgumentException("The new heap must be of type heap! Found: " + 
                                         heap.getSort());
    }
    if (!type.getSort().equals(Type.sort)) {
      throw new IllegalArgumentException("The type must be of type type! Found: " + 
                                         type.getSort());
    }
    if (!dim.getSort().equals(Num.sortInt)) {
      throw new IllegalArgumentException("The dimension must be of type integer! Found: " + 
                                         dim.getSort());
    }
    return Formula.lf.mkFnTerm(Formula.lf.symNewArray, 
                               new Term[] {oldheap, type, heap, loc, dim});

  }

  public static QuantVariableRef getLvVar() {
    return lvvar;
  }
}
