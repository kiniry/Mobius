package mobius.directVCGen.vcgen.expression;

import javafe.ast.Expr;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;

public abstract class ABasicExpressionVCGEn {
	private ExpressionVisitor visitor;
	public ABasicExpressionVCGEn(ExpressionVisitor vis) {
		visitor = vis;
	}
	public Post getPre(Expr e, VCEntry post) {
		return (Post)e.accept(visitor, post);
	}
}
