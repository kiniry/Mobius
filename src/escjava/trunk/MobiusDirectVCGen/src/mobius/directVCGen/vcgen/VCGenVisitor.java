package mobius.directVCGen.vcgen;

import javafe.ast.ClassDecl;
import javafe.ast.MethodDecl;

public class VCGenVisitor extends ABasicVisitor {


	
	public /*@non_null*/ Object visitClassDecl(/*@non_null*/ ClassDecl x, Object o) {
		System.out.println("Treating class: " + x.id);
		return visitTypeDecl(x, o);
	}
	
	public /*@non_null*/ Object visitMethodDecl(/*@non_null*/ MethodDecl x, Object o) {
		System.out.println("Method: " + x.id);
		return x.accept(new MethodVisitor(), o);
	}
	
}
