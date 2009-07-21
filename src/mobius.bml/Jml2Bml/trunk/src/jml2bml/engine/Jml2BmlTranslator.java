package jml2bml.engine;

import java.util.LinkedList;
import java.util.List;

import jml2bml.ast.ExtendedJmlTreeScanner;
import jml2bml.ast.SymbolsBuilder;
import jml2bml.rules.TranslationRule;
import jml2bml.symbols.Symbols;

import com.sun.source.tree.Tree;
import com.sun.tools.javac.util.Context;

/**
 * This visitor traverses the Tree and generates bml for jml annotations. All
 * the work is done in the preVisit method for the appropriate nodes. It tries
 * to apply all the defined rules. After an applicable rule (returned annotation
 * was not null) was found, next rules are not applied. User can define his own
 * translation rules. They have to extend the TranslationRule class and
 * overwrite appropriate visitXYZ methods. If such an rule is not applicable to
 * a node type, visit method for this node type should not be overwritten.
 *
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0-0.1
 *
 */
public class Jml2BmlTranslator extends
    ExtendedJmlTreeScanner < Symbols, Symbols > {
  /** Translation rules used. */
  private final List < TranslationRule > rules;

  /**
   * Application context.
   */
  private final Context context;

  /**
   * Creates a new instance of the Jml2BmlTranslator.
   * @param acontext
   */
  public Jml2BmlTranslator(final Context acontext) {
    this.context = acontext;
    this.rules = new LinkedList < TranslationRule >();
  }

  /**
   * This method invokes the rule - tries to apply it to the given node.
   * @param node visited node
   * @param v true, if we should try to apply the rule (we shouldn't if the
   * scanned node is a descendant of a node that we have already
   * translated
   * @return if the children should be visited
   */
  @Override
  protected Symbols preVisit(final Tree node, final Symbols v) {
    super.preVisit(node, v);
    final Symbols symbs = node.accept(new SymbolsBuilder(context), v);
    for (Class < ? > cl : JmlNodes.JML_CLASSES) {
      if (cl.isAssignableFrom(node.getClass())){
        for (TranslationRule < String, Symbols > rule : rules) {
          // try to apply the rule
          node.accept(rule, symbs);
        }
        return symbs;
      }
    }
    return symbs;
  }

  /**
   * All user defined rules should be registered using this method. Not
   * registered rules will not be applied.
   * @param rule rule to register.
   */
  public void registerTranslationRule(final TranslationRule rule) {
    rules.add(rule);
  }

}
