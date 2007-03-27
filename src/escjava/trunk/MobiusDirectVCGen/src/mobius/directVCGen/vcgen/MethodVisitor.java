package mobius.directVCGen.vcgen;

import javafe.ast.ASTNode;


public class MethodVisitor extends ABasicVisitor {
	@Override
	public Object visitASTNode(ASTNode x, Object o) {
		System.out.println(x + "\n{");
		int max = x.childCount();
		for(int i = 0; i < max; i++) {
			Object child = x.childAt(i);
			if(child instanceof ASTNode) {
				o = ((ASTNode) child).accept(this, o);
			}
		}
		System.out.println("}");
		return o;
	}
}
