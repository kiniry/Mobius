/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-10 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.rules;

import java.util.Vector;

import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.exceptions.NotTranslatedException;
import jml2bml.symbols.Symbols;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;

import annot.attributes.Exsure;
import annot.attributes.MethodSpecification;
import annot.attributes.SpecificationCase;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Formula;
import annot.bcexpression.modifies.ModifyList;
import annot.io.Code;

import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.util.Context;

/**
 * Translation rule for method specification.
 *
 * @author kjk (kjk@mimuw.edu.pl)
 *
 * @version 0-0.1
 */
public class SpecificationCaseRule extends TranslationRule<String, Symbols> {

  /**
   * Constructor.
   * @author kjk (kjk@mimuw.edu.pl)
   */
  private class SpecificationCaseBuilder extends
      TranslationRule<String, Symbols> {

    /**
     * Default preVisit method. Throws NotTranslatedException.
     * @param node visited node
     * @param symb symbol table
     * @return never reached.
     */
    protected String preVisit(final Tree node, final Symbols symb) {
      //TODO: change to screaming rule or sth??
      throw new NotTranslatedException("Not implemented: " + node);
    }

    public String visitJmlMethodClauseExpr(final JmlMethodClauseExpr node,
                                           final Symbols symb) {
      if (node.token == JmlToken.REQUIRES) {
        final AbstractFormula form = TranslationUtil
            .getFormula(node.expression, symb, myContext);
        if (precondition == null) {
          precondition = form;
        } else {
          precondition = new Formula(Code.AND, precondition, form);
        }
      } else if (node.token == JmlToken.ENSURES) {
        final AbstractFormula form = TranslationUtil
            .getFormula(node.expression, symb, myContext);
        
        if (postcondition == null) {
          postcondition = form;
        } else {
          postcondition = new Formula(Code.AND, precondition, form);
        }
      } else
        throw new NotTranslatedException("Not implemented: " + node);
      return "";
    }

    //    public String visitJmlMethodClauseSignals(final JmlMethodClauseSignals node,
    //                                              final Symbols symb) {
    //      final AbstractFormula form = BmlLibUtils.getFormula(node.expression,
    //                                                          symb, myContext);
    //      final BCExpression bcExpr = node.vardef.vartype.accept(RulesFactory
    //                                                    .getExpressionRule(myContext), symb);
    //      JCVariableDecl decl = node.vardef;
    //      //FIXME: add finding java type
    //      JavaReferenceType jType = null;
    //      Exsure exc = new Exsure(jType, null);
    //      if (excondition == null)
    //        excondition = new Vector<Exsure>();
    //      excondition.add(exc);
    //      return "";
    //    }
  }

  /**
   * application context.
   */
  private final Context myContext;

  /**
   * Creates a new instance of the rule.
   * @param context application context.
   */
  public SpecificationCaseRule(final Context context) {
    super();
    this.myContext = context;
  }

  private AbstractFormula precondition;

  private ModifyList modifies;

  private AbstractFormula postcondition;

  private Vector<Exsure> excondition;

  public String visitJmlSpecificationCase(final JmlSpecificationCase node,
                                          final Symbols symb) {
    //FIXME: should be cleaned?? one instance of rule per execution??
    precondition = null;
    modifies = null;
    postcondition = null;
    excondition = null;

    final BCClass bcClazz = symb.findClass();
    final TreeNodeFinder finder = myContext.get(TreeNodeFinder.class);
    final Tree specs = finder.getAncestor(node, JmlMethodSpecs.class);
    final Tree nextClassMember = finder.getNextSibling(specs);
    if (nextClassMember == null || nextClassMember.getKind() != Kind.METHOD)
      throw new NotTranslatedException("Cannot find method for the requires: "
                                       + node);
    final JmlMethodDecl method = (JmlMethodDecl) nextClassMember;
    //TODO: here make Specification case for Bmllib
    final BCMethod bcMethod = BytecodeUtil
        .findMethod(method.getName(), bcClazz);
    MethodSpecification spec = bcMethod.getMspec();
    if (spec == null) {
      spec = new MethodSpecification(bcMethod);
      bcMethod.setMspec(spec);
    }
    new SpecificationCaseBuilder().scan(node.clauses, symb);

    //FIXME: when only precondition = should go to empty spec case??
    final SpecificationCase specCase = new SpecificationCase(bcMethod,
                                                             precondition,
                                                             modifies,
                                                             postcondition,
                                                             excondition);
    spec.addCase(specCase);
    return "";
  }

  //  public String visitJmlMethodClauseExpr(JmlMethodClauseExpr node, Symbols symb) {
  //    if (node.token == JmlToken.REQUIRES) {
  //      if (node.expression == null)
  //        throw new NotTranslatedException("Expression is null");
  //      final BCClass bcClazz = symb.findClass();
  //      final TreeNodeFinder finder = myContext.get(TreeNodeFinder.class);
  //      
  //      //Finding method in tree
  //      Tree specs = finder.getAncestor(node, JmlMethodSpecs.class);
  //      Tree nextClassMember = finder.getNextSibling(specs);
  //      if (nextClassMember == null || nextClassMember.getKind() != Kind.METHOD)
  //        throw new NotTranslatedException("Cannot find method for the requires: "+ node);
  //      JmlMethodDecl method = (JmlMethodDecl)nextClassMember;
  //      
  //      final BCMethod bcMethod = BytecodeUtil.findMethod(method.getName(), bcClazz);
  //
  //      final BCExpression expression = node.expression.accept(RulesFactory.getExpressionRule(myContext),
  //                                                             symb);
  //      if (expression.getType1() != JavaBasicType.JavaBool)
  //        throw new NotTranslatedException("assert expression must be boolean");
  //      final AbstractFormula form = (AbstractFormula) expression;
  //
  //      MethodSpecification spec = bcMethod.getMspec();
  //      if (spec != null)
  //        throw new NotTranslatedException("Method specification already present - joining not implemented");
  //
  //      spec = new MethodSpecification(bcMethod, form, new SpecificationCase[0]);
  //      bcMethod.setMspec(spec);
  //    }
  //    return null;
  //  }
}
