package mobius.directVCGen.vcgen.expression;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import javafe.ast.Expr;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.vcgen.stmt.StmtVCGen;
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
	
	public Term getNewExcpPost(Term type, VCEntry post) {
		Post p = StmtVCGen.getExcpPost(type, post);
		QuantVariableRef e = Expression.rvar(Ref.sort);
		QuantVariableRef heap = Heap.newVar();
		return Logic.forall(e,
				Logic.forall(heap,
						Logic.implies(Logic.typeLE(Type.of(heap, e), type),
								Logic.implies(Heap.newElem(Heap.var, heap, e),
						 			p.substWith(e).subst(Heap.var, heap)))));
	}
}
