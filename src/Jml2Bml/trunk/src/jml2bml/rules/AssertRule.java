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
  private final Context my_context;

  public AssertRule(final Context context) {
    this.my_context = context;
  }

  /**
   * visiting Jml statement expression. If this node represents "assert" clause,
   * generate the corresponding bml annotation. In other cases return null.
   * @param node - node to visit
   * @param p - additional data (not used)
   * @return bml-assert annotation or null.
   */
  public String visitJmlStatementExpr(final JmlStatementExpr node, final Void p) {
    final String token = node.token.internedName();
    if (JmlTokens.ASSERT.equals(token)) {
      final TranslationRule expressionRule = RulesFactory
          .getExpressionRule(my_context);
      String expr = null;
      if (node.expression != null) {
        expr = node.expression.accept(expressionRule, p);
      }
      String optionalExpr = null;
      if (node.optionalExpression != null) {
        optionalExpr = node.optionalExpression.accept(expressionRule, p);
      }
      String ret = BmlKeywords.ASSERT + " ";
      if (expr != null) {
        ret += expr;
      }
      if (optionalExpr != null) {
        ret += optionalExpr;
      }
      return ret;

    }
    return null;
  }

}
