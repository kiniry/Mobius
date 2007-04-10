package mobius.directVCGen.vcgen;

import mobius.directVCGen.vcgen.intern.ABasicVisitor;
import javafe.ast.ClassDecl;
import javafe.ast.MethodDecl;
import javafe.ast.Stmt;

public class VCGenVisitor extends ABasicVisitor {


	
	public /*@non_null*/ Object visitClassDecl(/*@non_null*/ ClassDecl x, Object o) {
		System.out.println("Treating class: " + x.id);
		return visitTypeDecl(x, o);
	}
	
	public /*@non_null*/ Object visitMethodDecl(/*@non_null*/ MethodDecl x, Object o) {
		System.out.println("Method: " + x.id);
		Stmt.Annotation a;
		return x.accept(new MethodVisitor(x), o);
	}
	
}
