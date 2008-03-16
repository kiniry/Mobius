/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-10 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import java.util.Vector;

import jml2bml.ast.SymbolsBuilder;
import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.exceptions.NotTranslatedException;
import jml2bml.symbols.Symbols;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import annot.attributes.Exsure;
import annot.attributes.MethodSpecification;
import annot.attributes.SpecificationCase;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Formula;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.modifies.ModifyList;
import annot.io.Code;

import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
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
    @Override
    protected String preVisit(final Tree node, final Symbols symb) {
      throw new NotTranslatedException("Not implemented: " + node);
    }

    /**
     * Translation of JmlMethodClauseExpr node. This may be a requires node
     * {@code node.toek = JmlToke.REQUIRES}, or a ensures node
     * {@code node.toek = JmlToke.ENSURES}
     *
     * @param node node to translate.
     * @param symb current symbol table
     * @return empty string
     */
    @Override
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

    /**
     * Adds a new Exsure (signals) to current excondition.
     * @param exsure exsure to add to excondition.
     */
    private void appendExcondition(final Exsure exsure) {
      if (excondition == null)
        excondition = new Vector<Exsure>();
      excondition.add(exsure);
    }

    /**
     * This method processes signals clause in a specification case.
     *
     * @param node signals node to process.
     * @param symb current symbols table.
     * @return empty string
     */
    @Override
    public String visitJmlMethodClauseSignals(final JmlMethodClauseSignals node,
                                              final Symbols symb) {
      if (node.vardef.name == null) {
        final AbstractFormula form = TranslationUtil
            .getFormula(node.expression, symb, myContext);
        final JavaReferenceType type = new JavaReferenceType(node.vardef.vartype
                                                                 .toString());
        appendExcondition(new Exsure(type, form));
      } else
        throw new NotTranslatedException("Not implemented signals type: " +
                                         node.vardef);
      return "";
    }
  }

  /** Application context. */
  private final Context myContext;

  /** Precondition of the current specification case. */
  private AbstractFormula precondition;

  /** Modify list of the current specification case. */
  private ModifyList modifies;

  /** Postcondition of the current specification case. */
  private AbstractFormula postcondition;

  /** Raises list of the current specification case. */
  private Vector<Exsure> excondition;

  /**
   * Creates a new instance of the rule.
   * @param context application context.
   */
  public SpecificationCaseRule(final Context context) {
    super();
    this.myContext = context;
  }

  /**
   * Creates symbols table with method parameters.
   * @param symb symbol table
   * @param method the method which parameters will be added
   * @return new symbols table with method parameters added
   */
  private Symbols createSymbolsWithParams(final Symbols symb,
                                          final JmlMethodDecl method) {
    Symbols withParams = new Symbols(symb);
    final SymbolsBuilder sb = new SymbolsBuilder(myContext);
    for (JCVariableDecl varDecl : method.params)
      withParams = sb.visitJmlVariableDecl((JmlVariableDecl)varDecl,
                                           withParams);
    return withParams;
  }

  /**
   * This is a main translation method of the specification case.
   *
   * @param node The specification case node to translate.
   * @param symb Current symbol table.
   * @return empty string
   */
  @Override
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
      throw new NotTranslatedException("Cannot find method for the requires: " +
                                       node);
    final JmlMethodDecl method = (JmlMethodDecl) nextClassMember;
    final Symbols withParams = createSymbolsWithParams(symb, method);
    //TODO: here make Specification case for Bmllib
    final BCMethod bcMethod = BytecodeUtil.findMethod(method.getName(),
                                                      bcClazz);
    MethodSpecification spec = bcMethod.getMspec();
    if (spec == null) {
      spec = new MethodSpecification(bcMethod);
      bcMethod.setMspec(spec);
    }
    new SpecificationCaseBuilder().scan(node.clauses, withParams);

    //FIXME: when only precondition = should go to empty spec case??
    final SpecificationCase specCase = new SpecificationCase(bcMethod,
                                                             precondition,
                                                             modifies,
                                                             postcondition,
                                                             excondition);
    spec.addCase(specCase);
    return "";
  }
}
