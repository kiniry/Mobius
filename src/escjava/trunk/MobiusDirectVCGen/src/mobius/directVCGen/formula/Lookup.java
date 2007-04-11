package mobius.directVCGen.formula;

import java.util.Vector;

import escjava.sortedProver.Lifter.Term;
import javafe.ast.ClassDecl;
import javafe.ast.MethodDecl;

public class Lookup {

	/**
	 * Returns the FOL Term representation of the precondition of method m.
	 * @param m the method of interest
	 */
	public static Term precondition(MethodDecl m){
		return null;
	}

	/**
	 * Returns the FOL Term representation of the normal postcondition of method m.
	 * @param m the method of interest
	 */
	public static Term normal_postcondition(MethodDecl m){
		return null;
	}

	/**
	 * Returns a vector of   FOL Term representations of the exceptional postconditions of method m.
	 * The exceptional postcondition will always look like this: Sort => Term
	 * @param m the method of interest
	 */
	public static Vector<Term> exceptional_postconditions(MethodDecl m){
		return null;
	}

//	/**
//	 * Returns all annotations for method m
//	 * @param m the method of interest
//	 */
//	public static  method_annotation(MethodDecl m){
//		return null;
//	}
	
	public static Term invariant(ClassDecl c){
		return null;
	}
	
}
