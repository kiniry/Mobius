package mobius.directVCGen.vcgen;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.logic.Logic;
import mobius.directVCGen.vcgen.intern.ABasicVisitor;
import javafe.ast.BlockStmt;
import javafe.ast.MethodDecl;


public class MethodVisitor extends ABasicVisitor {
	MethodDecl meth;
	
	public MethodVisitor(MethodDecl x) {
		meth = x;
	}

	public /*@non_null*/ Object visitBlockStmt(/*@non_null*/ BlockStmt x, Object o) {
		IFormula post = Logic.TRUE;
		DirectVCGen dvcg = new DirectVCGen();
		System.out.println(x.accept(dvcg, post));
		
		return dvcg.vcs;
	}
	
}
