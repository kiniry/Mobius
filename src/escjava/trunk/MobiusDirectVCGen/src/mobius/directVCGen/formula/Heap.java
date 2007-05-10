package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

// TODO: add comments
public class Heap {
	// TODO: add comments
	public static Sort sort = Formula.lf.sortMap;
	// TODO: add comments
	public static QuantVariableRef varPre = Expression.rvar(Expression.old("heap"), sort);
	// TODO: add comments
	public static QuantVariableRef var = Expression.rvar("heap", sort);
	
	// TODO: add comments
	public static Term store(QuantVariableRef heap, QuantVariable var, Term val) {
		return Formula.lf.mkFnTerm(Formula.lf.symStore, new Term[] {heap, Expression.refFromVar(var), sortToValue(val)});
	}
	
	// TODO: add comments
	public static Term store(QuantVariableRef heap, Term obj, QuantVariable var, Term val) {
		return Formula.lf.mkFnTerm(Formula.lf.symDynStore, new Term[] {heap, obj, Expression.refFromVar(var), sortToValue(val)});
	}
	
	// TODO: add comments
	public static Term storeArray(QuantVariableRef heap, QuantVariableRef var, Term val, Term idx) {
		return Formula.lf.mkFnTerm(Formula.lf.symArrStore, new Term[] {heap,  var, sortToValue(val), idx});
	}
	
	// TODO: add comments
	public static Term select(QuantVariableRef heap, QuantVariable var) {
		Term select = Formula.lf.mkFnTerm(Formula.lf.symSelect, 
				new Term[] {heap, Expression.refFromVar(var)});
		return valueToSort(select, var.type);
	}
	
	// TODO: add comments
	public static Term select(QuantVariableRef heap, Term obj, QuantVariable var) {
		Term select = Formula.lf.mkFnTerm(Formula.lf.symDynSelect, 
				new Term[] {heap, obj, Expression.refFromVar(var)});
		return valueToSort(select, var.type);
	}
	
	// TODO: add comments
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

	// TODO: add comments
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
	
	// TODO: add comments
	private static int heapc =0;
	// TODO: add comments
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
