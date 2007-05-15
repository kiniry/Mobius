package mobius.directVCGen.formula;

import escjava.ast.TagConstants;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * This class is used to create the formulas of boolean type.
 */
public class Bool {

	/**
	 * Creates a binary term of the type bool. The type
	 * of the term can be bool or numerical. Typically it is
	 * used to generate {@link #equals(Term, Term)} or 
	 * {@link #notEquals(Term, Term)} terms.
	 * @param l the left part of the term
	 * @param r the right part of the term
	 * @param tag the tag representing the symbol associated 
	 * with the leaf
	 * @return a well formed and well typed term
	 */
	private static Term binaryOp(Term l, Term r, int tag) {
		if(l.getSort().equals(Bool.sort)) {
			return boolBinaryOp(l, r, tag);
		}
		else {
			return numBinaryOp(l, r, tag);
		}
	}
	
	/**
	 * Creates a binary term of type bool, over bool terms.
	 * It type-checks everything.
	 * @param l the left-side element of the term
	 * @param r the right-side element of the term
	 * @param tag the tag associated with the term
	 * @return a well-formed term well-typed et al
	 */
	private static Term boolBinaryOp(Term l, Term r, int tag){
		if(l.getSort() != Bool.sort || r.getSort() != Bool.sort)
			throw new IllegalArgumentException("The sorts of the arguments should be bool found: " + l.getSort() + 
					" and " + r + ".");
		FnTerm t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
		t.tag = tag;
		return t; 
	}
	
	/**
	 * Used to create a term of a unary boolean op. 
	 * For instance it is used in the case of the boolean
	 * negation.
	 * @param t the term which to apply the specified operator
	 * @param tag the tag of the operator
	 * @return a well formed and well typed term
	 */
	private static Term boolUnaryOp(Term t, int tag) {
		if(t.getSort() != Bool.sort )
			throw new IllegalArgumentException("The sorts of the arguments should be bool found: " + t.getSort());
		FnTerm res = Formula.lf.mkFnTerm(Formula.lf.symBoolUnaryFn, new Term[] {t});
		res.tag = tag;
		return res;
	}
	
	/**
	 * Build a term representing a binary boolean formula over numbers. 
	 * It type-checks the parameters and does the necessary promotions.
	 * @param l The left leaf
	 * @param r The right leaf of the term
	 * @param tag the tag representing the symbol associated with
	 * the term
	 * @return a well-formed and well-typed term
	 */
	private static Term numBinaryOp(Term l, Term r, int tag){
		if(l.getSort() != r.getSort() &&
				(!Num.isNum(l.getSort()) || !Num.isNum(r.getSort())))
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			if(r.getSort() == Num.sortReal) {
				l = Num.intToReal(l);
				t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
			}
			else {
				t = Formula.lf.mkFnTerm(Formula.lf.symIntBoolFn, new Term[] {l, r});
			}
			
		}
		else if (l.getSort() == Num.sortReal) {
			if(r.getSort() == Num.sortInt) {
				r = Num.intToReal(r);
			}
			t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		t.tag = tag;
		return t;
	}

	/** the sort representing the booleans */
	public static Sort sort = Formula.lf.sortBool;
		
	/**
	 * Returns the term representing the given value b.
	 * @param b The boolean value to convert to a term
	 * @return a BoolLiteral term
	 */
	public static Term value(Boolean b) {	
		return Formula.lf.mkBoolLiteral(b);
	}
	
	/**
	 * Returns the right equality from the argument type.
	 * @param l The left element of the equality
	 * @param r The right element of the equality
	 * @return an equality over the terms
	 * @throws IllegalArgumentException if the types of the arguments are bad.
	 */
	public static Term equals(Term l, Term r) {
		return binaryOp(l,r,NodeBuilder.predEQ);
	}	
	
	/**
	 * Returns the non equality from the argument type.
	 * @param l The left element of the non equality
	 * @param r The right element of non equality
	 * @return an non equality over the terms
	 * @throws IllegalArgumentException if the types of the arguments are bad.
	 */
	public static Term notEquals(Term l, Term r) {
		return binaryOp(l,r,NodeBuilder.predNE);
	}	
	
	/**
	 * Returns a boolean Or expression.
	 * @param l The left element of the expression
	 * @param r The right element of the expression
	 * @return a term representing a boolean or 
	 * a FnTerm with tag {@link TagConstants#BOOLOR}
	 */
	public static Term or(Term l, Term r) {
		return boolBinaryOp(l,r,TagConstants.BOOLOR);
	}
	 
	/**
	 * Returns a boolean and expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link TagConstants#BOOLAND}
	 */
	public static Term and(Term l, Term r) {
		return boolBinaryOp(l,r,TagConstants.BOOLAND);
	}

	/**
	 * Returns a boolean not expression.
	 * @param t the boolean expression to turn to a not
	 * @return A Not expression of type FnTerm with tag {@link TagConstants#BOOLNOT}
	 */
	public static Term not(Term t) {
		return boolUnaryOp(t,TagConstants.BOOLNOT);
	}

	/**
	 * Returns a boolean lesser or equal expression.
	 * @param l The left element of the expression
	 * @param r The right element of the expression
	 * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
	 */
	public static Term le(Term l, Term r) {
		return numBinaryOp(l,r,NodeBuilder.predLE);
	}

	/**
	 * Returns a boolean lesser than expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
	 */
	public static Term lt(Term l, Term r) {		
		return numBinaryOp(l,r,NodeBuilder.predLT);
	}

	/**
	 * Returns a boolean greater or equal expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
	 */
	public static Term ge(Term l, Term r) {		
		return numBinaryOp(l,r,NodeBuilder.predGE);
	}
	
	/**
	 * Returns a boolean greater than expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
	 */
	public static Term gt(Term l, Term r) {		
		return numBinaryOp(l,r,NodeBuilder.predGT);
	}
	
	
	/**
	 * Create an object representing a logical implies.
	 * @param f1 the first element of the implies
	 * @param f2 the second element of the implies
	 * @return a nicely created implies
	 */
	public static Term implies(Term f1, Term f2) {
		return boolBinaryOp(f1,f2, TagConstants.BOOLIMPLIES);
	}
	
	/**
	 * Create an object representing a logical full implies.
	 * @param f1 the first element of the full implies
	 * @param f2 the second element of the full implies
	 * @return a nicely created fullimplies
	 */
	public static Term fullImplies(Term f1, Term f2) {
		return boolBinaryOp(f1,f2, TagConstants.BOOLEQ);
	} 

}
