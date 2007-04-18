package mobius.directVCGen.vcgen;

import javafe.ast.ClassDecl;
import javafe.ast.MethodDecl;

/**
 * The main entry point of the vcgen
 * @author J. Charles
 */
public class DirectVCGen extends ABasicVisitor {


	
	public /*@non_null*/ Object visitClassDecl(/*@non_null*/ ClassDecl x, Object o) {
		System.out.println("Treating class: " + x.id);
		return visitTypeDecl(x, o);
	}
	
	public /*@non_null*/ Object visitMethodDecl(/*@non_null*/ MethodDecl x, Object o) {
		
		MethodVisitor mv = MethodVisitor.treatMethod(x);
		System.out.println(mv);
		return o;
	}
	
}
