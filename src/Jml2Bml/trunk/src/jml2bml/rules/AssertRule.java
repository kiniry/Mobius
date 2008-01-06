package jml2bml.rules;

import jml2bml.engine.BmlKeywords;
import jml2bml.engine.JmlTokens;

import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;

import com.sun.tools.javac.util.Context;

/**
 * Rule for translating jml asser clauses. Uses ExpressionRule inside.
 * @author Jedrek
 *
 */
public class AssertRule extends TranslationRule {
	private Context context;

	public AssertRule(Context context) {
		this.context = context;
	}

	@Override
	public String visitJmlStatementExpr(JmlStatementExpr node, Void p) {
		String token = node.token.internedName();
		if (JmlTokens.ASSERT.equals(token)) {
			TranslationRule expressionRule = RulesFactory
					.getExpressionRule(context);
			String expr = null;
			if (node.expression != null) {
				expr = node.expression.accept(expressionRule, p);
			}
			String optionalExpr = null;
			if (node.optionalExpression != null) {
				optionalExpr = node.optionalExpression
						.accept(expressionRule, p);
			}
			String ret = BmlKeywords.ASSERT + " ";
			if (expr != null)
				ret += expr;
			if (optionalExpr != null)
				ret += optionalExpr;
			return ret;

		}
		return null;
	}

}
