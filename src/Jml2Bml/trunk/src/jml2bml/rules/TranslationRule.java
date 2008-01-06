package jml2bml.rules;

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

public abstract class TranslationRule extends TreeScanner<String, Void>
		implements JmlTreeVisitor<String, Void> {
	

	protected String preVisit(Tree node, Void p) {
		return null;
	}

	public String visitCompilationUnit(CompilationUnitTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitImport(ImportTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitClass(ClassTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitMethod(MethodTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitVariable(VariableTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitEmptyStatement(EmptyStatementTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitBlock(BlockTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitDoWhileLoop(DoWhileLoopTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitWhileLoop(WhileLoopTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitForLoop(ForLoopTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitLabeledStatement(LabeledStatementTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitSwitch(SwitchTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitCase(CaseTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitSynchronized(SynchronizedTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitTry(TryTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitCatch(CatchTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitConditionalExpression(ConditionalExpressionTree node,
			Void p) {
		return preVisit(node, p);
	}

	public String visitIf(IfTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitExpressionStatement(ExpressionStatementTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitBreak(BreakTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitContinue(ContinueTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitReturn(ReturnTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitThrow(ThrowTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitAssert(AssertTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitMethodInvocation(MethodInvocationTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitNewClass(NewClassTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitNewArray(NewArrayTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitParenthesized(ParenthesizedTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitAssignment(AssignmentTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitUnary(UnaryTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitBinary(BinaryTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitTypeCast(TypeCastTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitInstanceOf(InstanceOfTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitArrayAccess(ArrayAccessTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitMemberSelect(MemberSelectTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitIdentifier(IdentifierTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitLiteral(LiteralTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitPrimitiveType(PrimitiveTypeTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitArrayType(ArrayTypeTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitParameterizedType(ParameterizedTypeTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitTypeParameter(TypeParameterTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitWildcard(WildcardTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitModifiers(ModifiersTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitAnnotation(AnnotationTree node, Void p) {
		return preVisit(node, p);
	}

	public String visitOther(Tree node, Void p) {
		return preVisit(node, p);
	}

	public String visitErroneous(ErroneousTree node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlBinary(JmlBinary node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlClassDecl(JmlClassDecl node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlCompilationUnit(JmlCompilationUnit node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlDoWhileLoop(JmlDoWhileLoop node, Void p) {
		return preVisit(node, p);

	}

	@Override
	public String visitJmlEnhancedForLoop(JmlEnhancedForLoop node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlForLoop(JmlForLoop node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlFunction(JmlFunction node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlGroupName(JmlGroupName node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlImport(JmlImport node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlLblExpression(JmlLblExpression node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodClauseAssignable(
			JmlMethodClauseAssignable node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodClauseConditional(
			JmlMethodClauseConditional node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodClauseDecl(JmlMethodClauseDecl node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodClauseExpr(JmlMethodClauseExpr node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodClauseGroup(JmlMethodClauseGroup node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly node,
			Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodClauseSignals(JmlMethodClauseSignals node,
			Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodDecl(JmlMethodDecl node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlMethodSpecs(JmlMethodSpecs node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlQuantifiedExpr(JmlQuantifiedExpr node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlRefines(JmlRefines node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlSetComprehension(JmlSetComprehension node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlSingleton(JmlSingleton node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlSpecificationCase(JmlSpecificationCase node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlStatement(JmlStatement node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlStatementDecls(JmlStatementDecls node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlStatementExpr(JmlStatementExpr node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlStatementLoop(JmlStatementLoop node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlStatementSpec(JmlStatementSpec node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlStoreRefArrayRange(JmlStoreRefArrayRange node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlStoreRefKeyword(JmlStoreRefKeyword node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlStoreRefListExpression(
			JmlStoreRefListExpression node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseConditional(JmlTypeClauseConditional node,
			Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseConstraint(JmlTypeClauseConstraint node,
			Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseDecl(JmlTypeClauseDecl node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseExpr(JmlTypeClauseExpr node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseIn(JmlTypeClauseIn node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseInitializer(JmlTypeClauseInitializer node,
			Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseMaps(JmlTypeClauseMaps node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor node,
			Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlTypeClauseRepresents(JmlTypeClauseRepresents node,
			Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlVariableDecl(JmlVariableDecl node, Void p) {
		return preVisit(node, p);
	}

	@Override
	public String visitJmlWhileLoop(JmlWhileLoop node, Void p) {
		return preVisit(node, p);
	}

}
