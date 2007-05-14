package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

// TODO: add comments
public class Heap {
	/** the sort that represents the type of a heap */
	public static Sort sort = Formula.lf.sortMap;
	
	// TODO: add comments
	public static QuantVariableRef var = Expression.rvar("heap", sort);
	// TODO: add comments
	public static QuantVariableRef varPre = Expression.old(var);
	
	// TODO: add comments
	public static Term store(QuantVariableRef heap, QuantVariable var, Term val) {
		return Formula.lf.mkFnTerm(Formula.lf.symStore, new Term[] {heap, Expression.rvar(var), sortToValue(val)});
	}
	
	// TODO: add comments
	public static Term store(QuantVariableRef heap, Term obj, QuantVariable var, Term val) {
		return Formula.lf.mkFnTerm(Formula.lf.symDynStore, new Term[] {heap, obj, Expression.rvar(var), sortToValue(val)});
	}
	
	// TODO: add comments
	public static Term storeArray(QuantVariableRef heap, Term var, Term idx, Term val) {
		if(!heap.getSort().equals(Heap.sort)) {
			throw new IllegalArgumentException("The heap argument should be of sort heap, found: " + heap.getSort());
		}
		if(!var.getSort().equals(Ref.sort)) {
			throw new IllegalArgumentException("The var argument should be of sort reference, found: " + var.getSort());
		}
		
		if(!idx.getSort().equals(Num.sortInt)) {
			throw new IllegalArgumentException("The idx argument should be of sort int, found: " + idx.getSort());
		}
		return Formula.lf.mkFnTerm(Formula.lf.symArrStore, new Term[] {heap,  var, idx, sortToValue(val)});
	}
	
	/**
	 * The select for a static field.
	 * @param heap the heap on which to do the select
	 * @param var the name of the field to select
	 * @return the term representing the select
	 */
	public static Term select(QuantVariableRef heap, QuantVariable var) {
		Term select = Formula.lf.mkFnTerm(Formula.lf.symSelect, 
				new Term[] {heap, Expression.rvar(var)});
		return valueToSort(select, var.type);
	}
	
	/**
	 * The select for a dynamic field.
	 * @param heap the heap on which to do the select
	 * @param obj the object to which the field belong
	 * @param var the name of the field on which to do the select
	 * @return the term representing the select
	 */
	public static Term select(QuantVariableRef heap, Term obj, QuantVariable var) {
		Term select = Formula.lf.mkFnTerm(Formula.lf.symDynSelect, 
				new Term[] {heap, obj, Expression.rvar(var)});
		return valueToSort(select, var.type);
	}
	
	public static Term selectArray(Term heap, Term var, Term idx, Sort type) {
		Term select = Formula.lf.mkFnTerm(Formula.lf.symArrSelect, new Term[] {heap, var, idx});
		return valueToSort(select, type);
	}
	
	
	/**
	 * Create a term that is a conversion from the value to the specified 
	 * sort.
	 * @param t the term to convert
	 * @param type the type to which to convert the term
	 * @return the conversion term
	 */
	private static Term valueToSort(Term t, Sort type) {
		if(type == Formula.lf.sortBool) {
			return Formula.lf.mkFnTerm(Formula.lf.symValueToBool,  new Term [] {t});
		}
		else if(type == Formula.lf.sortRef) {
			return Formula.lf.mkFnTerm(Formula.lf.symValueToRef,  new Term [] {t});
		}
		else if(type == Formula.lf.sortInt) {
			return Formula.lf.mkFnTerm(Formula.lf.symValueToInt,  new Term [] {t});
		}
		else if(type == Formula.lf.sortReal) {
			return Formula.lf.mkFnTerm(Formula.lf.symValueToReal,  new Term [] {t});
		}
		else {
			throw new IllegalArgumentException("Bad type " +
					"found: " + type);
		}
	}

	/**
	 * It cast a variable of any sort to a value.
	 * @param t the variable to convert to a value
	 * @return the converted variable
	 */
	public static Term sortToValue(Term t) {
		Sort s = t.getSort();
		s = s.theRealThing();
		if(s.equals(Formula.lf.sortBool)) {
			return Formula.lf.mkFnTerm(Formula.lf.symBoolToValue,  new Term [] {t});
		}
		else if(s.equals(Formula.lf.sortRef)) {
			return Formula.lf.mkFnTerm(Formula.lf.symRefToValue,  new Term [] {t});
		}
		else if(s.equals(Formula.lf.sortInt)) {
			return Formula.lf.mkFnTerm(Formula.lf.symIntToValue,  new Term [] {t});
		}
		else if(s.equals(Formula.lf.sortReal)) {
			return Formula.lf.mkFnTerm(Formula.lf.symRealToValue,  new Term [] {t});
		}
		else {
			throw new IllegalArgumentException("Bad type " +
					"found for " + t.getClass() + " " + t + ": " + t.getSort());
		}
	}
	
	/** the counter to count the number of instanciation of the heap variable */
	private static int heapc =0;
	
	/**
	 * Creates and return a new instance of the heap variable.
	 * @return a new heap variable
	 */
	public static QuantVariableRef newVar() {
		return Expression.rvar("heap" + (heapc++), Heap.sort);
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
	public static Term newObject(Term oldheap, Term type, Term heap,  QuantVariableRef e) {
		if(!oldheap.getSort().equals(Heap.sort)) {
			throw new IllegalArgumentException("The old heap must be of type heap! Found: " + oldheap.getSort());
		}
		if(!heap.getSort().equals(Heap.sort)) {
			throw new IllegalArgumentException("The new heap must be of type heap! Found: " + heap.getSort());
		}
		if(!type.getSort().equals(Type.sort)) {
			throw new IllegalArgumentException("The type must be of type type! Found: " + type.getSort());
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
	public static Term newArray(QuantVariableRef oldheap,  Term type, QuantVariableRef heap, Term dim, QuantVariableRef loc) {
		if(!oldheap.getSort().equals(Heap.sort)) {
			throw new IllegalArgumentException("The old heap must be of type heap! Found: " + oldheap.getSort());
		}
		if(!heap.getSort().equals(Heap.sort)) {
			throw new IllegalArgumentException("The new heap must be of type heap! Found: " + heap.getSort());
		}
		if(!type.getSort().equals(Type.sort)) {
			throw new IllegalArgumentException("The type must be of type type! Found: " + type.getSort());
		}
		if(!dim.getSort().equals(Num.sortInt)) {
			throw new IllegalArgumentException("The dimension must be of type integer! Found: " + dim.getSort());
		}
		return Formula.lf.mkFnTerm(Formula.lf.symNewArray, new Term[] {oldheap, type, heap, loc, dim});

	}


}
