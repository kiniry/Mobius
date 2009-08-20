package mobius.prover.simplify;

import mobius.prover.gui.editor.BasicTextAttribute;
import mobius.prover.gui.editor.IColorConstants;
import mobius.prover.gui.editor.detector.ExprDetector;
import mobius.prover.gui.editor.detector.WordDetector;
import mobius.prover.plugins.AProverTranslator;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

public class ProverTranslator extends AProverTranslator implements IColorConstants {

  // Colors...
  Color TAG_COLOR = 
    new Color(Display.getCurrent(), new RGB(100, 0, 100));
  Color STRING_COLOR = 
    new Color(Display.getCurrent(), new RGB(0, 0, 200));
  Color COMMENT_COLOR = 
    new Color(Display.getCurrent(), new RGB(0, 100, 0));
  Color LEMMA_COLOR = 
    new Color(Display.getCurrent(), new RGB(200, 30, 30));
  Color LIGHTGREY = 
    new Color(Display.getCurrent(), new RGB(230, 230, 230));
  // Some tokens
  IToken instr = new Token(new BasicTextAttribute(BLUE));
  IToken command = new Token(new BasicTextAttribute(DARKRED));
  IToken pats = new Token(new BasicTextAttribute(PINK));

  IToken comment = new Token(new BasicTextAttribute(COMMENT_COLOR));
  IToken def = new Token(new BasicTextAttribute(DEFAULT_TAG_COLOR));
  
  private IRule [] parsingRules;
  private IRule [] fileRules;

  private IRule[] initParsingRules() {

    final WordRule wexpr = new WordRule(new ParenDetector(), SENTENCE_TOKEN);
    final IRule [] rules = {
      new EndOfLineRule(";", COMMENT_TOKEN),
      wexpr
    };
    return rules;
  }
  @Override
  public String[] getCompilingCommand(String comp, String[] path, String file) {
    return new String [] {comp, file};
  }

  @Override
  public String[] getIdeCommand(String ide, String[] path, String file) {
    return new String [] {ide, file};
  }

  @Override
  public IRule[] getParsingRules() {
    if (parsingRules == null) {
      parsingRules = initParsingRules();
    }
    return parsingRules;
  }

  @Override
  public IRule[] getProverStateRules() {
    return new IRule [] {};
  }

  
  private IRule [] initFileRules() {
    final WordRule wr = new WordRule(new WordDetector(), def);
   
    wr.addWord("BG_PUSH", command);
    wr.addWord("DEFPRED", command);
    wr.addWord("PROMPT_OFF", command);
    wr.addWord("PROMPT_ON", command);
    
    wr.addWord("PATS", pats);
    wr.addWord("MPAT", pats);
    String []  instruc = new String [] {"FORALL", "EQ", "NEQ", "NOT", "IMPLIES",
                                        "AND", "OR", "IFF", "DISTINCT", "EXPLIES"};
    for (int i = 0; i < instruc.length; i++) {
      wr.addWord(instruc[i], instr);
    }
    
    final IRule [] rules = {
      new EndOfLineRule(";", comment),
      wr//,
      //wexpr
    };
    return rules;
  }
 
  /** {@inheritDoc} */
  @Override
  public IRule [] getProverTheoryRules() {
    if (fileRules == null) {
      fileRules = initFileRules();
    }
    return fileRules;
  }
  

  @Override
  public boolean isErrorMsg(String s) {
    // TODO Auto-generated method stub
    return false;
  }

}
