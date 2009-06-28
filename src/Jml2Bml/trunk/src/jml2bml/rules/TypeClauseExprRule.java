/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-27 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import javax.lang.model.element.Modifier;

import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;

import annot.attributes.clazz.ClassInvariant;
import annot.bcclass.BCClass;
import annot.bcexpression.formula.AbstractFormula;

import com.sun.tools.javac.util.Context;

/**
 * JmlTypeClauseExpr translation rule, now it works only
 * with invariant case.
 *
 * @author kjk (kjk@mimuw.edu.pl)
 *
 * @version 0.0-1
 */
public class TypeClauseExprRule extends TranslationRule<String, Symbols> {
  /** Context object. */
  private final Context myContext;

  /**
   * Constructor of the rule.
   * @param context context object
   */
  public TypeClauseExprRule(final Context context) {
    super();
    this.myContext = context;
  }

  /**
   * Main translation method.  The translation
   * realises the following logic:
   * <pre>
   *  Tr(invariantkeyword predicate, translationcontext) =
   *      replace(translationcontext,
   *         getInvariant(translationcontext),
   *         packInvariant(
   *            getInvExpression(
   *              getInvariant(translationcontext)) &&^*
   *            getExpression(Tr(predicate, translationcontext ))))
   * </pre>
   *
   * @param node node to be translated
   * @param symb symbol table
   * @return empty string
   */
  @Override
  public String visitJmlTypeClauseExpr(final JmlTypeClauseExpr node,
                                       final Symbols symb) {
    if (node.token == JmlToken.INVARIANT) {
      final BCClass clazz = symb.findClass();
      final AbstractFormula formula = TranslationUtil
              .getFormula(node.expression, symb, myContext);
      final boolean isstatic =
        node.modifiers.getFlags().contains(Modifier.STATIC);
      final ClassInvariant classInvariant =
        new ClassInvariant(clazz, formula, !isstatic);
      clazz.setInvariant(classInvariant);
    } else
      throw new NotTranslatedRuntimeException(
        "Token != invariant - not implemented");
    return "";
  }
}
