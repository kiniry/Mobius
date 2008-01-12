/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-10 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.engine.Symbols;
import jml2bml.exceptions.NotTranslatedException;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;

import annot.attributes.MethodSpecification;
import annot.attributes.SpecificationCase;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.javatype.JavaBasicType;

import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.util.Context;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 */
public class RequiresRule extends TranslationRule<String, Symbols> {
  private final Context myContext;

  public RequiresRule(final Context context) {
    this.myContext = context;
  }

  public String visitJmlMethodClauseExpr(JmlMethodClauseExpr node, Symbols symb) {
    if (node.token == JmlToken.REQUIRES) {
      if (node.expression == null)
        throw new NotTranslatedException("Expression is null");
      final BCClass bcClazz = myContext.get(BCClass.class);
      final TreeNodeFinder finder = myContext.get(TreeNodeFinder.class);
      
      //Finding method in tree
      Tree specs = finder.getAncestor(node, JmlMethodSpecs.class);
      Tree nextClassMember = finder.getNextMember(specs);
      if (nextClassMember == null || nextClassMember.getKind() != Kind.METHOD)
        throw new NotTranslatedException("Cannot find method for the requires: "+ node);
      JmlMethodDecl method = (JmlMethodDecl)nextClassMember;
      
      final BCMethod bcMethod = BytecodeUtil.findMethod(method.getName(), bcClazz);

      final BCExpression expression = node.expression.accept(RulesFactory.getExpressionRule(myContext),
                                                             symb);
      if (expression.getType1() != JavaBasicType.JavaBool)
        throw new NotTranslatedException("assert expression must be boolean");
      final AbstractFormula form = (AbstractFormula) expression;

      MethodSpecification spec = bcMethod.getMspec();
      if (spec != null)
        throw new NotTranslatedException("Method specification already present - joining not implemented");

      spec = new MethodSpecification(bcMethod, form, new SpecificationCase[0]);
      bcMethod.setMspec(spec);
    }
    return null;
  }
}
