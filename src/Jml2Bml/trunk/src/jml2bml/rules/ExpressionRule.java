package jml2bml.rules;

import jml2bml.bytecode.BytecodeUtils;
import jml2bml.engine.JmlTokens;
import jml2bml.engine.KeywordTranslator;
import jml2bml.engine.Utils;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.ConditionalExpression;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.formula.QuantifiedFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.ReadAttributeException;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.ParenthesizedTree;
import com.sun.source.tree.PrimitiveTypeTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;

/**
 * Rule for translating JML expressions.
 * @author Jedrek
 *
 */
public class ExpressionRule extends TranslationRule<BCExpression, Void> {

  public ExpressionRule(final Context context) {
  }

  // ------- visitor methods
  // TODO probably more nodes should be visited here
  @Override
  public BCExpression visitBinary(BinaryTree node, Void p) {
    BCExpression lhs = scan(node.getLeftOperand(), p);
    BCExpression rhs = scan(node.getRightOperand(), p);
    int operator = Utils.mapJCOperatorToBmlLib(node.getKind());
    return new ArithmeticExpression(operator, lhs, rhs);
  }

  @Override
  public BCExpression visitIdentifier(IdentifierTree node, Void p) {
    // FIXME translate identifier properly!
    return node.getName().toBCExpression();
  };

  @Override
  public BCExpression visitLiteral(LiteralTree node, Void p) {
    Kind kind = node.getKind();
    if (kind == Kind.INT_LITERAL)
      return new NumberLiteral(((Integer) node.getValue()).intValue());
    throw new RuntimeException("Not implemented literal: " + node);
  };

  @Override
  public BCExpression visitConditionalExpression(ConditionalExpressionTree node,
                                           Void p) {
    BCExpression condition = scan(node.getCondition(), p);
    BCExpression trueExpr = scan(node.getTrueExpression(), p);
    BCExpression falseExpr = scan(node.getFalseExpression(), p);
    return new ConditionalExpression(condition, trueExpr, falseExpr);

  }

  @Override
  public BCExpression visitParenthesized(ParenthesizedTree node, Void p) {
    return scan(node.getExpression(), p);
  }

  @Override
  public BCExpression visitJmlQuantifiedExpr(JmlQuantifiedExpr node, Void p) {
    int quantifierType = Utils.mapJCOperatorToBmlLib(node.op);
    QuantifiedFormula formula = new QuantifiedFormula(quantifierType);
    JavaBasicType type = (JavaBasicType)scan(node.localtype, p);
    for (Name name : node.names){
      //FIXME what is the second parameter?
      int index = 0;
      BoundVar var = new BoundVar(type,index,formula,name.toString());
      formula.addVariable(var);
    }
    final BCExpression predicate = scan(node.predicate, p);
    formula.setFormula(predicate);
    return formula;
  }

  @Override
  public BCExpression visitJmlBinary(JmlBinary node, Void p) {
    BCExpression lhs = scan(node.getLeftOperand(), p);
    BCExpression rhs = scan(node.getRightOperand(), p);
    int operator = Utils.mapJCOperatorToBmlLib(node.op);
    return new ArithmeticExpression(operator, lhs, rhs);
  }
  
  @Override
  public BCExpression visitPrimitiveType(PrimitiveTypeTree node, Void p) {
    try {
    return JavaType.getJavaBasicType(Utils.mapJCTypeKindToBmlLib(node.getPrimitiveTypeKind()));
    }catch (ReadAttributeException e){
      return null;
      //FIXME handle the exception
    }
    
  }
}
