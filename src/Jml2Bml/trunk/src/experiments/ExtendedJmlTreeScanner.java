package experiments;

import org.jmlspecs.openjml.JmlTreeVisitor;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlFunction;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseAssignable;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSigOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlPrimitiveTypeTree;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlRefines;
import org.jmlspecs.openjml.JmlTree.JmlSetComprehension;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementDecls;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefListExpression;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMonitorsFor;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;

import com.sun.source.tree.AnnotationTree;
import com.sun.source.tree.ArrayAccessTree;
import com.sun.source.tree.ArrayTypeTree;
import com.sun.source.tree.AssertTree;
import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.BlockTree;
import com.sun.source.tree.BreakTree;
import com.sun.source.tree.CaseTree;
import com.sun.source.tree.CatchTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.CompoundAssignmentTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.ContinueTree;
import com.sun.source.tree.DoWhileLoopTree;
import com.sun.source.tree.EmptyStatementTree;
import com.sun.source.tree.EnhancedForLoopTree;
import com.sun.source.tree.ErroneousTree;
import com.sun.source.tree.ExpressionStatementTree;
import com.sun.source.tree.ForLoopTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.IfTree;
import com.sun.source.tree.ImportTree;
import com.sun.source.tree.InstanceOfTree;
import com.sun.source.tree.LabeledStatementTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.ModifiersTree;
import com.sun.source.tree.NewArrayTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.ParameterizedTypeTree;
import com.sun.source.tree.ParenthesizedTree;
import com.sun.source.tree.PrimitiveTypeTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.SwitchTree;
import com.sun.source.tree.SynchronizedTree;
import com.sun.source.tree.ThrowTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.TryTree;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.TypeParameterTree;
import com.sun.source.tree.UnaryTree;
import com.sun.source.tree.VariableTree;
import com.sun.source.tree.WhileLoopTree;
import com.sun.source.tree.WildcardTree;
import com.sun.source.util.TreeScanner;

/**
 * This class adds to the TreeScanner<R,P> the preVisit method (invoked at the
 * beginning of all visitXYZ methods)
 * 
 * @author Jedrek
 * 
 * @param <R>
 * @param
 *            <P>
 */
public class ExtendedJmlTreeScanner<R, P> extends TreeScanner<R, P> implements
		JmlTreeVisitor<R, P> {

	private R scanAndReduce(Tree node, P p, R r) {
		return reduce(scan(node, p), r);
	}

	private R scanAndReduce(Iterable<? extends Tree> nodes, P p, R r) {
		return reduce(scan(nodes, p), r);
	}

	protected P preVisit(Tree node, P p) {
		return p;
	}

	public R visitCompilationUnit(CompilationUnitTree node, P p) {
		p = preVisit(node, p);
		return super.visitCompilationUnit(node, p);
	}

	public R visitImport(ImportTree node, P p) {
		p = preVisit(node, p);
		return super.visitImport(node, p);
	}

	public R visitClass(ClassTree node, P p) {
		p = preVisit(node, p);
		return super.visitClass(node, p);
	}

	public R visitMethod(MethodTree node, P p) {
		p = preVisit(node, p);
		return super.visitMethod(node, p);
	}

	public R visitVariable(VariableTree node, P p) {
		p = preVisit(node, p);
		return super.visitVariable(node, p);
	}

	public R visitEmptyStatement(EmptyStatementTree node, P p) {
		p = preVisit(node, p);
		return super.visitEmptyStatement(node, p);
	}

	public R visitBlock(BlockTree node, P p) {
		p = preVisit(node, p);
		return super.visitBlock(node, p);
	}

	public R visitDoWhileLoop(DoWhileLoopTree node, P p) {
		p = preVisit(node, p);
		return super.visitDoWhileLoop(node, p);
	}

	public R visitWhileLoop(WhileLoopTree node, P p) {
		p = preVisit(node, p);
		return super.visitWhileLoop(node, p);
	}

	public R visitForLoop(ForLoopTree node, P p) {
		p = preVisit(node, p);
		return super.visitForLoop(node, p);
	}

	public R visitEnhancedForLoop(EnhancedForLoopTree node, P p) {
		p = preVisit(node, p);
		return super.visitEnhancedForLoop(node, p);
	}

	public R visitLabeledStatement(LabeledStatementTree node, P p) {
		p = preVisit(node, p);
		return super.visitLabeledStatement(node, p);
	}

	public R visitSwitch(SwitchTree node, P p) {
		p = preVisit(node, p);
		return super.visitSwitch(node, p);
	}

	public R visitCase(CaseTree node, P p) {
		p = preVisit(node, p);
		return super.visitCase(node, p);
	}

	public R visitSynchronized(SynchronizedTree node, P p) {
		p = preVisit(node, p);
		return super.visitSynchronized(node, p);
	}

	public R visitTry(TryTree node, P p) {
		p = preVisit(node, p);
		return super.visitTry(node, p);
	}

	public R visitCatch(CatchTree node, P p) {
		p = preVisit(node, p);
		return super.visitCatch(node, p);
	}

	public R visitConditionalExpression(ConditionalExpressionTree node, P p) {
		p = preVisit(node, p);
		return super.visitConditionalExpression(node, p);
	}

	public R visitIf(IfTree node, P p) {
		p = preVisit(node, p);
		return super.visitIf(node, p);
	}

	public R visitExpressionStatement(ExpressionStatementTree node, P p) {
		p = preVisit(node, p);
		return super.visitExpressionStatement(node, p);
	}

	public R visitBreak(BreakTree node, P p) {
		p = preVisit(node, p);
		return super.visitBreak(node, p);
	}

	public R visitContinue(ContinueTree node, P p) {
		p = preVisit(node, p);
		return super.visitContinue(node, p);
	}

	public R visitReturn(ReturnTree node, P p) {
		p = preVisit(node, p);
		return super.visitReturn(node, p);
	}

	public R visitThrow(ThrowTree node, P p) {
		p = preVisit(node, p);
		return super.visitThrow(node, p);
	}

	public R visitAssert(AssertTree node, P p) {
		p = preVisit(node, p);
		return super.visitAssert(node, p);
	}

	public R visitMethodInvocation(MethodInvocationTree node, P p) {
		p = preVisit(node, p);
		return super.visitMethodInvocation(node, p);
	}

	public R visitNewClass(NewClassTree node, P p) {
		p = preVisit(node, p);
		return super.visitNewClass(node, p);
	}

	public R visitNewArray(NewArrayTree node, P p) {
		p = preVisit(node, p);
		return super.visitNewArray(node, p);
	}

	public R visitParenthesized(ParenthesizedTree node, P p) {
		p = preVisit(node, p);
		return super.visitParenthesized(node, p);
	}

	public R visitAssignment(AssignmentTree node, P p) {
		p = preVisit(node, p);
		return super.visitAssignment(node, p);
	}

	public R visitCompoundAssignment(CompoundAssignmentTree node, P p) {
		p = preVisit(node, p);
		return super.visitCompoundAssignment(node, p);
	}

	public R visitUnary(UnaryTree node, P p) {
		p = preVisit(node, p);
		return super.visitUnary(node, p);
	}

	public R visitBinary(BinaryTree node, P p) {
		p = preVisit(node, p);
		return super.visitBinary(node, p);
	}

	public R visitTypeCast(TypeCastTree node, P p) {
		p = preVisit(node, p);
		return super.visitTypeCast(node, p);
	}

	public R visitInstanceOf(InstanceOfTree node, P p) {
		p = preVisit(node, p);
		return super.visitInstanceOf(node, p);
	}

	public R visitArrayAccess(ArrayAccessTree node, P p) {
		p = preVisit(node, p);
		return super.visitArrayAccess(node, p);
	}

	public R visitMemberSelect(MemberSelectTree node, P p) {
		p = preVisit(node, p);
		return super.visitMemberSelect(node, p);
	}

	public R visitIdentifier(IdentifierTree node, P p) {
		p = preVisit(node, p);
		return super.visitIdentifier(node, p);
	}

	public R visitLiteral(LiteralTree node, P p) {
		p = preVisit(node, p);
		return super.visitLiteral(node, p);
	}

	public R visitPrimitiveType(PrimitiveTypeTree node, P p) {
		p = preVisit(node, p);
		return super.visitPrimitiveType(node, p);
	}

	public R visitArrayType(ArrayTypeTree node, P p) {
		p = preVisit(node, p);
		return super.visitArrayType(node, p);
	}

	public R visitParameterizedType(ParameterizedTypeTree node, P p) {
		p = preVisit(node, p);
		return super.visitParameterizedType(node, p);
	}

	public R visitTypeParameter(TypeParameterTree node, P p) {
		p = preVisit(node, p);
		return super.visitTypeParameter(node, p);
	}

	public R visitWildcard(WildcardTree node, P p) {
		p = preVisit(node, p);
		return super.visitWildcard(node, p);
	}

	public R visitModifiers(ModifiersTree node, P p) {
		p = preVisit(node, p);
		return super.visitModifiers(node, p);
	}

	public R visitAnnotation(AnnotationTree node, P p) {
		p = preVisit(node, p);
		return super.visitAnnotation(node, p);
	}

	public R visitOther(Tree node, P p) {
		p = preVisit(node, p);
		return super.visitOther(node, p);
	}

	public R visitErroneous(ErroneousTree node, P p) {
		p = preVisit(node, p);
		return super.visitErroneous(node, p);
	}

	@Override
	public R visitJmlBinary(JmlBinary node, P p) {
		p = preVisit(node, p);
		R r = scan(node.lhs, p);
		r = scanAndReduce(node.rhs, p, r);
		return r;
	}

	@Override
	public R visitJmlClassDecl(JmlClassDecl node, P p) {
		p = preVisit(node, p);
		return super.visitClass(node, p);
	}

	@Override
	public R visitJmlCompilationUnit(JmlCompilationUnit node, P p) {
		p = preVisit(node, p);
		return super.visitCompilationUnit(node, p);
	}

	@Override
	public R visitJmlDoWhileLoop(JmlDoWhileLoop node, P p) {
		p = preVisit(node, p);
		R r = scan(node.loopSpecs, p);
		R r1 = super.visitDoWhileLoop(node, p);
		return reduce(r, r1);

	}

	@Override
	public R visitJmlEnhancedForLoop(JmlEnhancedForLoop node, P p) {
		p = preVisit(node, p);
		R r = scan(node.loopSpecs, p);
		R r1 = super.visitEnhancedForLoop(node, p);
		return reduce(r, r1);
	}

	@Override
	public R visitJmlForLoop(JmlForLoop node, P p) {
		p = preVisit(node, p);
		R r = scan(node.loopSpecs, p);
		R r1 = super.visitForLoop(node, p);
		return reduce(r, r1);
	}

	@Override
	public R visitJmlFunction(JmlFunction node, P p) {
		p = preVisit(node, p);
		return null;
	}

	@Override
	public R visitJmlGroupName(JmlGroupName node, P p) {
		p = preVisit(node, p);
		R r = scan(node.selection, p);
		return r;
	}

	@Override
	public R visitJmlImport(JmlImport node, P p) {
		p = preVisit(node, p);
		R r = super.visitImport(node, p);
		return r;
	}

	@Override
	public R visitJmlLblExpression(JmlLblExpression node, P p) {
		p = preVisit(node, p);
		return scan(node.expression, p);
	}

	@Override
	public R visitJmlMethodClauseAssignable(JmlMethodClauseAssignable node, P p) {
		p = preVisit(node, p);
		return scan(node.list, p);
	}

	@Override
	public R visitJmlMethodClauseConditional(JmlMethodClauseConditional node,
			P p) {
		p = preVisit(node, p);
		R r = scan(node.expression, p);
		return scanAndReduce(node.predicate, p, r);
	}

	@Override
	public R visitJmlMethodClauseDecl(JmlMethodClauseDecl node, P p) {
		p = preVisit(node, p);
		return scan(node.stats, p);
	}

	@Override
	public R visitJmlMethodClauseExpr(JmlMethodClauseExpr node, P p) {
		p = preVisit(node, p);
		return scan(node.expression, p);
	}

	@Override
	public R visitJmlMethodClauseGroup(JmlMethodClauseGroup node, P p) {
		p = preVisit(node, p);
		return scan(node.cases, p);
	}

	@Override
	public R visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly node, P p) {
		p = preVisit(node, p);
		return scan(node.list, p);
	}

	@Override
	public R visitJmlMethodClauseSignals(JmlMethodClauseSignals node, P p) {
		p = preVisit(node, p);
		return scan(node.expression, p);
	}

	@Override
	public R visitJmlMethodDecl(JmlMethodDecl node, P p) {
		p = preVisit(node, p);
		return super.visitMethod(node, p);
	}

	@Override
	public R visitJmlMethodSpecs(JmlMethodSpecs node, P p) {
		p = preVisit(node, p);
		return scan(node.cases, p);
	}

	@Override
	public R visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree node, P p) {
		p = preVisit(node, p);
		return null;
	}

	@Override
	public R visitJmlQuantifiedExpr(JmlQuantifiedExpr node, P p) {
		p = preVisit(node, p);
		R r = scan(node.localtype, p);
		r = scanAndReduce(node.range, p, r);
		r = scanAndReduce(node.modifiers, p, r);
		return scanAndReduce(node.predicate, p, r);
	}

	@Override
	public R visitJmlRefines(JmlRefines node, P p) {
		p = preVisit(node, p);
		return null;
	}

	@Override
	public R visitJmlSetComprehension(JmlSetComprehension node, P p) {
		p = preVisit(node, p);
		R r = scan(node.newtype, p);
		r = scanAndReduce(node.variable, p, r);
		return scanAndReduce(node.predicate, p, r);
	}

	@Override
	public R visitJmlSingleton(JmlSingleton node, P p) {
		p = preVisit(node, p);
		return null;
	}

	@Override
	public R visitJmlSpecificationCase(JmlSpecificationCase node, P p) {
		p = preVisit(node, p);
		R r = scan(node.clauses, p);
		return scanAndReduce(node.modifiers, p, r);
	}

	@Override
	public R visitJmlStatement(JmlStatement node, P p) {
		p = preVisit(node, p);
		return scan(node.statement, p);
	}

	@Override
	public R visitJmlStatementDecls(JmlStatementDecls node, P p) {
		p = preVisit(node, p);
		return scan(node.list, p);
	}

	@Override
	public R visitJmlStatementExpr(JmlStatementExpr node, P p) {
		p = preVisit(node, p);
		R r = scan(node.expression, p);
		r = scanAndReduce(node.optionalExpression, p, r);
		return r;
	}

	@Override
	public R visitJmlStatementLoop(JmlStatementLoop node, P p) {
		p = preVisit(node, p);
		return scan(node.expression, p);
	}

	@Override
	public R visitJmlStatementSpec(JmlStatementSpec node, P p) {
		p = preVisit(node, p);
		return scan(node.statementSpecs, p);
	}

	@Override
	public R visitJmlStoreRefArrayRange(JmlStoreRefArrayRange node, P p) {
		p = preVisit(node, p);
		R r = scan(node.expression, p);
		r = scanAndReduce(node.lo, p, r);
		r = scanAndReduce(node.hi, p, r);
		return r;
	}

	@Override
	public R visitJmlStoreRefKeyword(JmlStoreRefKeyword node, P p) {
		p = preVisit(node, p);
		return null;
	}

	@Override
	public R visitJmlStoreRefListExpression(JmlStoreRefListExpression node, P p) {
		p = preVisit(node, p);
		return scan(node.list, p);
	}

	@Override
	public R visitJmlTypeClauseConditional(JmlTypeClauseConditional node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		r = scanAndReduce(node.identifier, p, r);
		return scanAndReduce(node.expression, p, r);
	}

	@Override
	public R visitJmlTypeClauseConstraint(JmlTypeClauseConstraint node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		r = scanAndReduce(node.expression, p, r);
		r = scanAndReduce(node.sigs, p, r);
		return r;
	}

	@Override
	public R visitJmlTypeClauseDecl(JmlTypeClauseDecl node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		return scanAndReduce(node.decl, p, r);
	}

	@Override
	public R visitJmlTypeClauseExpr(JmlTypeClauseExpr node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		r = scanAndReduce(node.expression, p, r);
		return r;

	}

	@Override
	public R visitJmlTypeClauseIn(JmlTypeClauseIn node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		r = scanAndReduce(node.list, p, r);
		return r;

	}

	@Override
	public R visitJmlTypeClauseInitializer(JmlTypeClauseInitializer node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		return scanAndReduce(node.specs, p, r);
	}

	@Override
	public R visitJmlTypeClauseMaps(JmlTypeClauseMaps node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		r = scanAndReduce(node.expression, p, r);
		return scanAndReduce(node.list, p, r);
	}

	@Override
	public R visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		r = scanAndReduce(node.identifier, p, r);
		return scanAndReduce(node.list, p, r);
	}

	@Override
	public R visitJmlTypeClauseRepresents(JmlTypeClauseRepresents node, P p) {
		p = preVisit(node, p);
		R r = scan(node.modifiers, p);
		r = scanAndReduce(node.ident, p, r);
		return scanAndReduce(node.expression, p, r);
	}

	@Override
	public R visitJmlVariableDecl(JmlVariableDecl node, P p) {
		p = preVisit(node, p);
		return super.visitVariable(node, p);
	}

	@Override
	public R visitJmlWhileLoop(JmlWhileLoop node, P p) {
		p = preVisit(node, p);
		R r = scan(node.loopSpecs, p);
		R r1 = super.visitWhileLoop(node, p);
		return reduce(r, r1);
	}

}
