package mobius.directVCGen.vcgen;

import escjava.sortedProver.Lifter.Term;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.vcgen.intern.ABasicVisitor;
import javafe.ast.BlockStmt;
import javafe.ast.MethodDecl;


public class MethodVisitor extends ABasicVisitor {
	MethodDecl meth;
	
	public MethodVisitor(MethodDecl x) {
		meth = x;
	}

	public /*@non_null*/ Object visitBlockStmt(/*@non_null*/ BlockStmt x, Object o) {
		Term post = Logic.True();
		DirectVCGen dvcg = new DirectVCGen();
		System.out.println(x.accept(dvcg, post));
		
		return dvcg.vcs;
	}
	
}
