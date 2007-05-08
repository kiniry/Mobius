package mobius.directVCGen.formula;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Vector;

import mobius.directVCGen.vcgen.struct.Post;

import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.FnSymbol;
import escjava.sortedProver.NodeBuilder.Sort;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.MethodDecl;
import javafe.ast.RoutineDecl;

public class Lookup {
	public static Vector<FnSymbol> symToDeclare = new Vector<FnSymbol>();
	public static HashSet<QuantVariable> fieldsToDeclare = new HashSet<QuantVariable>();
	
	public static HashMap<RoutineDecl, Term> preconditions = new HashMap<RoutineDecl, Term>();
	public static HashMap<RoutineDecl, Post> postconditions = new HashMap<RoutineDecl, Post>();
	
	public static Term buildStdCond (RoutineDecl m, String name, boolean hasResult) {
		int arity = m.args.size();
		boolean incThis = false;
		
		Sort returnType = Ref.sort;  
		if(m instanceof MethodDecl) {
			returnType = Type.typeToSort(((MethodDecl) m).returnType);
			if((m.getModifiers() & Modifiers.ACC_STATIC) == 0) {
				arity ++;
				incThis = true;
			}
		}
		
		if((m instanceof ConstructorDecl) ||
				((MethodDecl)m).returnType.getTag() == TagConstants.VOIDTYPE) {
			hasResult = false;
		}
		if(hasResult) {
			arity++;
		}
		Sort [] s = new Sort[arity];
		Term [] args = new Term [arity];
		if(incThis) {
			s [0] = Ref.sort;
			args[0] = Ref.varthis;
		}
		FormalParaDeclVec v = m.args;
		for(int i = 0; i < v.size(); i ++) {
			FormalParaDecl para = v.elementAt(i);
			args[i + 1] = Expression.rvar(para);
			s[i + 1] = args[i+1].getSort();
			
		}
		if(hasResult) {
			args[args.length - 1] = Expression.rvar(Expression.result, returnType);
			s[s.length - 1] = args[args.length - 1].getSort();
		}
		if(m instanceof ConstructorDecl) {
			name = ((ConstructorDecl)m).parent.id + name;
		}
		else {
			name = ((MethodDecl)m).id+ name;
		}
		FnSymbol sym = Formula.lf.registerPredSymbol(name, s);
		symToDeclare.add(sym);
		
		return Formula.lf.mkFnTerm(sym, args);
		
	}
	/**
	 * Returns the FOL Term representation of the precondition of method m.
	 * @param m the method of interest
	 */
	public static Term precondition(RoutineDecl m){
		
		return buildStdCond (m, "_pre", false);
	}

	/**
	 * Returns the FOL Term representation of the normal postcondition of method m.
	 * @param m the method of interest
	 */
	public static Post normalPostcondition(RoutineDecl m){
		return new Post(buildStdCond (m, "_norm", true)); 
	}
	public static Post normalPostcondition(MethodDecl m){
		return new Post(Expression.rvar(Expression.result, Type.typeToSort(m.returnType)),buildStdCond (m, "_norm", true)); 
	}
	/**
	 * Returns a vector of   FOL Term representations of the exceptional postconditions of method m.
	 * The exceptional postcondition will always look like this: Sort => Term
	 * @param m the method of interest
	 */
	public static Post exceptionalPostcondition(RoutineDecl m){
		return new Post(Expression.rvar(Expression.result, Ref.sort),buildStdCond (m, "_excp", false)); 
	}
	
	public static Term invariant(ClassDecl c){
		return Logic.True();
	}
	
}
