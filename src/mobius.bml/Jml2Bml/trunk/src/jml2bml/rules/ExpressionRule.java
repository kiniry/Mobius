/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.rules;

import javax.lang.model.type.TypeKind;

import jml2bml.ast.TreeNodeFinder;
import jml2bml.bmllib.BmlLibUtils;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.bytecode.TypeSignature;
import jml2bml.exceptions.Jml2BmlException;
import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;
import jml2bml.symbols.Variable;
import jml2bml.utils.Constants;
import jml2bml.utils.JCUtils;

import org.apache.bcel.generic.ConstantPoolGen;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.ArrayAccess;
import annot.bcexpression.ArrayLength;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.ConditionalExpression;
import annot.bcexpression.FieldAccess;
import annot.bcexpression.NONNULLELEMENTS;
import annot.bcexpression.NULL;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.OLD;
import annot.bcexpression.RESULT;
import annot.bcexpression.THIS;
import annot.bcexpression.TYPEsmall;
import annot.bcexpression.formula.Formula;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.formula.Predicate2Ar;
import annot.bcexpression.formula.QuantifiedFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.bcexpression.modifies.ModifyExpression;
import annot.io.Code;
import annot.io.ReadAttributeException;

import com.sun.source.tree.ArrayAccessTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.ParenthesizedTree;
import com.sun.source.tree.PrimitiveTypeTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.UnaryTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;

/**
 * Rule for translating JML expressions.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @author kjk    (kjk@mimuw.edu.pl)
 * @version 0.0-1
 *
 */
public class ExpressionRule extends TranslationRule < BCExpression, Symbols > {
  /**
   * application context.
   */
  private Context myContext;

  /**
   * Creates new instance of the ExpressionRule.
   * @param context application context.
   */
  public ExpressionRule(final Context context) {
    myContext = context;
  }

  // ------- visitor methods
  /**
   * Default preVisit - throws NotTranslatedRuntimeException.
   * @param node visited node
   * @param p symbol table
   * @return never reached
   */
  @Override
  protected BCExpression preVisit(final Tree node, final Symbols p) {
    throw new NotTranslatedRuntimeException("Node " + node +
                                            " not translated.");
  }

  // TODO probably more nodes should be visited here
  /**
   * Creates an BCExpression for Binary Tree node.
   * @param node node to translate
   * @param p symbol table
   * @return translated node
   */
  @Override
  public BCExpression visitBinary(final BinaryTree node, final Symbols p) {
    final BCExpression lhs = scan(node.getLeftOperand(), p);
    final BCExpression rhs = scan(node.getRightOperand(), p);
    final int operator = BmlLibUtils.translateBinaryOperator(node.getKind());
    //TODO: (kjk) This should be done better!!
    if (BmlLibUtils.isBinaryOperatorPredicate2Ar(operator)) {
      return new Predicate2Ar(operator, lhs, rhs);
    } else {
      return new ArithmeticExpression(operator, lhs, rhs);
    }
  }

  @Override
  public BCExpression visitUnary(final UnaryTree node, final Symbols p) {
    final BCExpression expr = scan(node.getExpression(), p);
    final int operator = BmlLibUtils.translateUnaryOperator(node.getKind());
    return new Formula(operator, expr);
  }

  /**
   * Creates an BCExpression for IdentifierTree node.
   * @param node node to translate
   * @param p symbol table
   * @return translated node
   */
  @Override
  public BCExpression visitIdentifier(final IdentifierTree node,
                                      final Symbols p) {
    final String name = node.getName().toString();
    if (Constants.THIS.equals(name)) {
      return new THIS(p.findClass());
    }
    final Variable variable = p.get(name);
    if (variable == null) {
      throw new Jml2BmlException("Invalid variable " + name);
    }
    if (variable.isBoundVariable()) {
      return variable.getVariable();
    }
    if (variable.isLocalVariable()) {
      return variable.getVariable();
    }
    if (variable.isField()) {
      final JCIdent i = (JCIdent) node;
      //field access is handled in a different way:
      //(cannot be taken from the symbol table, we have to know,
      //whether it's old or not
      return BytecodeUtil.createFieldRef(i.sym, p.findClass());
    }
    return null;
  };

  @Override
  public BCExpression visitJmlStoreRefKeyword(
      final org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword node,
      final Symbols p) {
    if (node.token == JmlToken.BSNOTHING)
      return ModifyExpression.NOTHING_MODIF;
    if (node.token == JmlToken.BSEVERYTHING)
      return ModifyExpression.EVERYTHING_MODIF;
    return null;
  };

  /**
   * This method handles the Literal node.
   * @param node - node to handle
   * @param p - symbol table at this point
   *
   * @return parsed Literal. Currently only int,
   * boolean and null-literals are parsed
   */
  @Override
  public BCExpression visitLiteral(final LiteralTree node, final Symbols p) {
    final Kind kind = node.getKind();
    if (kind == Kind.INT_LITERAL) {
      return new NumberLiteral(((Integer) node.getValue()).intValue());
    }
    if (kind == Kind.BOOLEAN_LITERAL) {
      return new Predicate0Ar(((Boolean) node.getValue()).booleanValue());
    }
    if (kind == Kind.NULL_LITERAL) {
      return new NULL();
    }
    if (kind == Kind.STRING_LITERAL) {
      //FIXME find out how string literals are represented
    }
    throw new NotTranslatedRuntimeException("Not implemented literal: " + node);
  };

  /**
   * Handling conditional expressions ( cond ? trueExpr : falseExpr ).
   * @param node - node to parse
   * @param p - symbol table at current point
   * @return parsed expression
   */
  @Override
  public BCExpression visitConditionalExpression(
      final ConditionalExpressionTree node,
      final Symbols p) {
    final BCExpression condition = scan(node.getCondition(), p);
    final BCExpression trueExpr = scan(node.getTrueExpression(), p);
    final BCExpression falseExpr = scan(node.getFalseExpression(), p);
    return new ConditionalExpression(condition, trueExpr, falseExpr);

  }

  /**
   * Visits parenthised expression.
   * @param node node to visit
   * @param p symbol table
   * @return translated node
   */
  @Override
  public BCExpression visitParenthesized(final ParenthesizedTree node,
                                         final Symbols p) {
    return scan(node.getExpression(), p);
  }

  /**
   * Handling quantified expressions.
   * @param node - node to parse
   *= @param p - sybmol table at this point
   * (it will be extended here, by adding bounded variables)
   * @return parsed expression
   */
  @Override
  public BCExpression visitJmlQuantifiedExpr(final JmlQuantifiedExpr node,
                                             final Symbols p) {
    final int quantifierType = BmlLibUtils.mapJCOperatorToBmlLib(node.op);
    final QuantifiedFormula formula = new QuantifiedFormula(quantifierType);
    final Symbols symbols = new Symbols(p);
    for (JCVariableDecl var: node.decls) {
      final JavaBasicType type = (JavaBasicType) scan(var.getType(), p);
      final String name = var.getName().toString();
      final int nameAndTypeIdx = p.findClass().getCp().getCoombinedCP().addNameAndType(name, TypeSignature.getSignature(var.type));
      final BoundVar bvar = new BoundVar(type, nameAndTypeIdx,
                                        formula, name.toString());
      formula.addVariable(bvar);
      symbols.put(name.toString(), new Variable(bvar));
    }
    final BCExpression predicate = scan(node.value, symbols);
    formula.setFormula(predicate);
    return formula;
  }

  /**
   * Creates an BCExpression for JmlBinary node.
   * @param node node to translate
   * @param p symbol table
   * @return translated node
   */
  @Override
  public BCExpression visitJmlBinary(final JmlBinary node, final Symbols p) {
    final BCExpression lhs = scan(node.getLeftOperand(), p);
    final BCExpression rhs = scan(node.getRightOperand(), p);
    final int operator = BmlLibUtils.mapJCOperatorToBmlLib(node.op);
    if (BmlLibUtils.isBinaryOperatorPredicate2Ar(operator)) {
      return new Predicate2Ar(operator, lhs, rhs);
    }

    return new ArithmeticExpression(operator, lhs, rhs);
  }

  /**
   * Creates an BCExpression for Primitive Typ node.
   * @param node node to translate
   * @param p symbol table
   * @return translated node
   */
  @Override
  public BCExpression visitPrimitiveType(final PrimitiveTypeTree node,
                                         final Symbols p) {
    try {
      return JavaType.getJavaBasicType(BmlLibUtils.mapJCTypeKindToBmlLib(node
          .getPrimitiveTypeKind()));
    } catch (ReadAttributeException e) {
      throw new RuntimeException(e);
    }

  }

  /**
   * Creates an BCExpression for Member Select node (<code>a.b</code>).
   * Method calls are not supported.
   * @param node node to translate
   * @param p symbol table
   * @return translated node
   */
  @Override
  public BCExpression visitMemberSelect(final MemberSelectTree node,
                                        final Symbols p) {
    BCExpression constant = TranslationUtil.handleConstant(((JCFieldAccess) node).sym);
    if (constant != null)
      return constant;
    
    //FIXME no function calls supported
    final BCExpression expr = scan(node.getExpression(), p);
    final Type type = ((JCTree) node).type;
    final Type ctype = ((JCTree.JCFieldAccess) node).selected.type;
    final String identifier = node.getIdentifier().toString();
    if (type.getKind() == TypeKind.ARRAY && Constants.ARRAY_LENGTH.equals(identifier))
        return new ArrayLength(expr);
    //simplest case - there exist also in java code the same field access
    final ConstantPoolGen cp = p.findClass().getCp().getCoombinedCP();
    final int fieldRefIndex = cp.addFieldref(ctype.toString(), identifier, TypeSignature.getSignature(ctype));
    return new FieldAccess(Code.FIELD_ACCESS, expr, BmlLibUtils
                           .createFieldRef(fieldRefIndex, p.findClass()));
  }

  /**
   * Handling array access a[k].
   * @param node - node to translate
   * @param p - symbol table
   * @return parsed node
   */
  @Override
  public BCExpression visitArrayAccess(final ArrayAccessTree node,
                                       final Symbols p) {
    return new ArrayAccess(scan(node.getExpression(), p), scan(node.getIndex(),
                                                               p));
  }

  /**
   * Creates an BCExpression for Method invocation node.
   * It can recognize only \old (no normal methods supported).
   * @param node node to translate
   * @param p symbol table
   * @return translated node
   */
  @Override
  public BCExpression visitJmlMethodInvocation(final JmlMethodInvocation node,
                                               final Symbols p) {
    if (node.token == JmlToken.BSOLD){
      final BCExpression expr = scan(node.getArguments(), p);
      return new OLD(expr);
    } else if (node.token == JmlToken.BSTYPELC) {
      JCIdent expr = (JCIdent)node.getArguments().head;
      JavaType type = JavaType.getJavaType(TypeSignature.getSignature(((TypeSymbol) expr.sym).type));
      return new TYPEsmall(type);
    } else if (node.token == JmlToken.BSNONNULLELEMENTS) {
      final BCExpression expr = scan(node.getArguments(), p);
      return new NONNULLELEMENTS(expr);
    }
    
    throw new NotTranslatedRuntimeException("Method invocation not supported!"+node);
  }

  /**
   * Creates an BCExpression for JmlSingleton node.
   * Only \result is supported.
   * @param node node to translate
   * @param p symbol table
   * @return translated node
   */
  @Override
  public BCExpression visitJmlSingleton(final JmlSingleton node,
                                        final Symbols p) {
    if (JCUtils.isResult(node)) {
      final BCClass bcClazz = p.findClass();
      final TreeNodeFinder finder = myContext.get(TreeNodeFinder.class);
      final Tree specs = finder.getAncestor(node, JmlMethodSpecs.class);
      final Tree methodTree = finder.getParent(specs);
      if (methodTree == null || methodTree.getKind() != Kind.METHOD)
        throw new NotTranslatedRuntimeException(
          "Cannot find method for the \result: " + node);
      final JmlMethodDecl method = (JmlMethodDecl) methodTree;
      final BCMethod bcMethod = BytecodeUtil.findMethod(method, bcClazz);
      return new RESULT(bcMethod);
    }
    throw new NotTranslatedRuntimeException("Singleton type not translated: " +
                                            node);
  }
  
}
