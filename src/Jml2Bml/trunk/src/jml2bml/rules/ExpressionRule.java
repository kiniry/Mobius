package jml2bml.rules;

import jml2bml.bytecode.BytecodeUtils;
import jml2bml.engine.JmlTokens;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.ParenthesizedTree;
import com.sun.tools.javac.util.Context;

/**
 * Rule for translating JML expressions.
 * @author Jedrek
 *
 */
public class ExpressionRule extends TranslationRule
		{
	private BytecodeUtils bytecodeUtils;

	
	public ExpressionRule(Context context) {
		bytecodeUtils = context.get(BytecodeUtils.class);
	}


	// ------- visitor methods
	// TODO probably more nodes should be visited here
	@Override
	public String visitBinary(BinaryTree node, Void p) {
		String lhs = scan(node.getLeftOperand(), p);
		String rhs = scan(node.getRightOperand(), p);
		String operator = JmlTokens.operatorName(node.getKind());
		return lhs + operator + rhs;
	}

	@Override
	public String visitIdentifier(IdentifierTree node, Void p) {
		// FIXME translate identifier properly!
		return node.getName().toString();
	};

	@Override
	public String visitLiteral(LiteralTree node, Void p) {
		return node.toString();

	};

	@Override
	public String visitConditionalExpression(ConditionalExpressionTree node,
			Void p) {
		String condition = scan(node.getCondition(), p);
		String trueExpr = scan(node.getTrueExpression(), p);
		String falseExpr = scan(node.getFalseExpression(), p);
		return condition + " ? " + trueExpr + " : " + falseExpr;
		
	}
		
	@Override
	public String visitParenthesized(ParenthesizedTree node, Void p) {
		return "(" + scan(node.getExpression(), p) + ")";
	}

}
