package jml2bml.rules;

import jml2bml.bytecode.BytecodeUtils;
import jml2bml.engine.BmlKeywords;
import jml2bml.engine.JmlTokens;
import jml2bml.engine.KeywordTranslator;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.ParenthesizedTree;
import com.sun.source.tree.PrimitiveTypeTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;

/**
 * Rule for translating JML expressions.
 * @author Jedrek
 *
 */
public class ExpressionRule extends TranslationRule {
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

  @Override
  public String visitJmlQuantifiedExpr(JmlQuantifiedExpr node, Void p) {
    String quantifyType = BmlKeywords.EXISTS;
    if (JmlTokens.FORALL.equals(node.op.name().toString())) {
      quantifyType = BmlKeywords.FORALL;
    } else if (JmlTokens.FORALL.equals(node.op.name().toString())) {
      quantifyType = BmlKeywords.EXISTS;
    }
    String localType = scan(node.localtype, p);
    String names = "";
    for (Name name : node.names) {
      String n = name.toString();
      if (n.length() > 0) {
        if (names.length() > 0){
          names += ",";
        }
        names += n;
      }
    }
    if (names.length() >0)
      names += "; ";
    final String predicate = scan(node.predicate, p);
    return quantifyType + " " +localType + " " + names+ predicate;
  }

  @Override
  public String visitJmlBinary(JmlBinary node, Void p) {
    String lhs = scan(node.getLeftOperand(), p);
    String rhs = scan(node.getRightOperand(), p);
    String operator = KeywordTranslator.translate(node.op.name());
    return lhs + operator + rhs;
  }
  
  @Override
  public String visitPrimitiveType(PrimitiveTypeTree node, Void p) {
    return node.getPrimitiveTypeKind().toString();
    
  }
}
