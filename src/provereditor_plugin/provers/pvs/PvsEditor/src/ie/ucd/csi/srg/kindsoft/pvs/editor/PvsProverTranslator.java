package ie.ucd.csi.srg.kindsoft.pvs.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WordRule;

import prover.gui.editor.IColorConstants;
import prover.gui.editor.detector.ExprDetector;
import prover.gui.editor.detector.WordDetector;
import prover.plugins.AProverTranslator;

public class PvsProverTranslator extends AProverTranslator implements IPvsColorConstants {

  private final class ConsequentComponentDetector implements IWordDetector {
    public boolean isWordStart(char c) {
     return c == '{';
    }

    public boolean isWordPart(char c) {
      return c == '}' || Character.isDigit(c);
    }
  }

  private final class PrecedentComponentDetector implements IWordDetector {
    public boolean isWordStart(char c) {
     return c == '{';
    }

    public boolean isWordPart(char c) {
      return c == '}' || Character.isDigit(c) || c == '-';
    }
  }

  // @todo jrk Just stick in all reserved words for now then refine to the different 
  // classifications below so that we can highlight different keywords and operators in
  // different ways.  E.g., an outfix overloadable operator might be RED and ITALIC.
  private static final String[] pvs_reserved_words = { "CHALLENGE", "CLAIM", "CONJECTURE", "COROLLARY", 
      "FACT", "FORMULA","LAW", "LEMMA", "LEMMA", "PROPOSITION", "SUBLEMMA", "THEOREM" };
  
  private static final String[] pvs_formula_keywords = { "CHALLENGE", "CLAIM", "CONJECTURE", "COROLLARY", 
    "FACT", "FORMULA","LAW", "LEMMA", "LEMMA", "PROPOSITION", "SUBLEMMA", "THEOREM" };
  
  private static final String[] pvs_overloadable_symbols = { };
  
  private static final String[] pvs_nonoverloadable_symbols = { };
  
  private static final String[] pvs_outfix_symbols = { };
  
  private static final String[] pvs_infix_symbols = { };
  
  // @todo jrk Refine this method to better match what we did in the fancy PVS front-end.
  public String[][] getUnicodeReplacements() {
    return super.getUnicodeReplacements();
  }
 
  // @todo jrk Refine this method to better match what we did in the fancy PVS front-end.
  public String[][] getReplacements() {
    return super.getReplacements();
  }

  public IRule[] getProverStateRules() {
     // Highlight all consequences in a different way than the precedences.
    final WordRule consequence_rule =
        new WordRule(new ConsequentComponentDetector(), consequent);
    consequence_rule.setColumnConstraint(0);
    final WordRule precedent_rule =
      new WordRule(new PrecedentComponentDetector(), precedent);
    precedent_rule.setColumnConstraint(0);
    // Replace the turnstile by a bigger turnstile.
    final IRule[] result = {
        new SingleLineRule("|-------", null, turnstile),
        consequence_rule,
        precedent_rule
    };
    return result;
  }
     
  public IRule[] getProverTheoryRules() {
    WordRule reserved_words_rule = new WordRule(new WordDetector(), def);
    for (int i = 0; i < pvs_reserved_words.length; i++) {
      reserved_words_rule.addWord(pvs_reserved_words[i], tag);
    }
    WordRule wexpr = new WordRule(new ExprDetector(), tag);
    IRule[] rules = {
        new MultiLineRule("\"", "\"", string),
        new SingleLineRule("%", null, comment),
        new SingleLineRule("\"", "\"", string),
        reserved_words_rule,
        wexpr
    };
    return rules;
  }
 
  public IRule[] getParsingRules() {
    //@ assert false;
    // @todo Implement this method.
    assert false : "This method is not yet implemented.";
    return null;
  }

  public boolean isErrorMsg(String s) {
    return s != null || (s.indexOf("pvs-err") != -1);
  }
 
  public String[] getIdeCommand(String ide, String[] path, String file) {
    String[] result = { ide, file };
    return result;
  }
  
  public String[] getCompilingCommand(String comp, String[] path, String file) {
    String[] result = { "/bin/sh", "-c", 
        "echo \\\"(progn" +
        "(in-package :pvs)" +
        "(setq pvs::*noninteractive* t)" +
        "(setq pvs::*pvs-verbose* $VERBOSE)" +
        "(setq pvs::current-prefix-arg t)" +
        "(pvs::pvs-init)" +
        "(pvs::change-context \\\\\\\"" + path[0] + "\\\\\\\" t)" +
        "(pvs::typecheck-file \\\\\\\"" + file + "\\\\\\\" nil nil nil)" +
        "(pvs::save-context)" +
        "(fresh-line)" +
        "(excl:exit 0 :no-unwind t :quiet t))\\\" | " + comp + " -raw -nobg" };
    return result;
  }

}
