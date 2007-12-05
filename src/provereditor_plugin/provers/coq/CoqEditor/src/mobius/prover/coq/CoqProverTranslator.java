package mobius.prover.coq;

import java.io.InputStream;
import java.util.regex.Pattern;

import mobius.prover.coq.utils.CoqConstructFinder;
import mobius.prover.coq.utils.ICoqColorConstants;
import mobius.prover.gui.editor.FixedSizeWordRule;
import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.detector.ExprDetector;
import mobius.prover.gui.editor.detector.WordDetector;
import mobius.prover.gui.editor.outline.types.ProverType;
import mobius.prover.plugins.AProverTranslator;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;


public class CoqProverTranslator extends AProverTranslator implements ICoqColorConstants {
  
  /** the current instance of the translator. */
  public static final CoqProverTranslator instance = new CoqProverTranslator();
  
  /** the typical vernaculars strings. */
  public static final String [] vernac = {
    "forall", "Proof",
    "Load", "Require", "Qed", "Import", "Open", "Scope", 
    "match", "end", "Section", "End" 
  };
  
  public static final String [] lem = {
    "Definition", "Variable", "Lemma", "Fixpoint", "Axiom", "Hypothesis", "Inductive"
  };
       
  /** the replacements for given strings. */
  public static final String [][] replacements = {
    {"\ufffd", " "},
    {"([0-9]+) subgoals", "\n\n\\Subgoals :"},
    {"([0-9]+) subgoal", "\n\n\\Subgoal :"},
    {"============================",
      "-----------------------------------------------------------------------------------"
    }
  };  
  
  private static final Pattern [] [] pats = {
    {Pattern.compile("\\s*Module Type\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
    {Pattern.compile("\\s*Module\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
    {Pattern.compile("\\s*Definition\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
    {Pattern.compile("\\s*Lemma\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
    {Pattern.compile("\\s*Fixpoint\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
    {Pattern.compile("\\s*Axiom\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
    {Pattern.compile("\\s*Parameter\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
    {Pattern.compile("\\s*Inductive\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
    {Pattern.compile("\\s*Variable\\s*"), Pattern.compile("[a-zA-Z_0-9]*")},
  };
  

  private IRule [] proofRules;
  private IRule [] fileRules;
  private IRule [] parsingRules;


  public static Image [] imgs;
  
  
  public static AProverTranslator getInstance() {
    return instance;
  }
  
  /** {@inheritDoc} */
  @Override
  public String [][] getReplacements() {
    return replacements;
  }

  private IRule [] initFileRules() {
    final WordRule wr = new WordRule(new WordDetector(), def);
    for (int i = 0; i < vernac.length; i++) {
      wr.addWord(vernac[i], tag);
    }
    for (int i = 0; i < lem.length; i++) {
      wr.addWord(lem[i], lemma);
    }
    final WordRule wexpr = new WordRule(new ExprDetector(), tag);
    wexpr.addWord(".", tag);
    final IRule [] rules = {
      new MultiLineRule("(*", "*)", comment),
      new MultiLineRule("\"", "\"", string),
      new SingleLineRule("(*", "*)", comment),
      new SingleLineRule("\"", "\"", string),
      wr,
      wexpr
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
  
  
  private IRule [] initProofRules() {
    final WordRule wr = new WordRule(new WordDetector(), def);
    for (int i = 0; i < vernac.length; i++) {
      wr.addWord(vernac[i], tag);
    }
    for (int i = 0; i < lem.length; i++) {
      wr.addWord(lem[i], lemma);
    }
    final WordRule wexpr = new WordRule(new ExprDetector(), tag);
    wexpr.addWord(".", tag);
    final WordRule hypothesis = new WordRule(new WordDetector(), comment);
    hypothesis.setColumnConstraint(2);

    final SingleLineRule subg = new SingleLineRule("Subgoal", ":", completed);
    subg.setColumnConstraint(0);
    final MultiLineRule mlr = new MultiLineRule("subgoal", "", subgoal2, (char) 0, true);
    mlr.setColumnConstraint(0);
    final IRule [] rules = {
      new SingleLineRule("Proof ", "completed", completed),
      subg, mlr, hypothesis,
      new MultiLineRule("forall ", ",", forall),
      new MultiLineRule("exists ", ",", forall),
      new MultiLineRule("(*", "*)", comment),
      new MultiLineRule("\"", "\"", string),
      new SingleLineRule("(*", "*)", comment),
      new SingleLineRule("\"", "\"", string),
      wr, wexpr
    };
    return rules;
  }
  
  /** {@inheritDoc} */
  @Override
  public IRule [] getProverStateRules() {        
    if (proofRules == null) {
      proofRules = initProofRules();
    }
    return proofRules;
  }

  private IRule[] initParsingRules() {
    final WordRule endofsentence = new FixedSizeWordRule(new IWordDetector() {

      public boolean isWordStart(final char c) {
        return c == '.';
      }

      public boolean isWordPart(final char c) {
        return Character.isWhitespace(c);
      }
      
    }, 2);

    endofsentence.addWord(". ", SENTENCE_TOKEN);
    endofsentence.addWord(".\n", SENTENCE_TOKEN);
    endofsentence.addWord(".\t", SENTENCE_TOKEN);
    
    final IRule [] rules = {
      new MultiLineRule("(*", "*)", COMMENT_TOKEN),
      new MultiLineRule("\"", "\"", COMMENT_TOKEN),

      new SingleLineRule("(*", "*)", COMMENT_TOKEN),
      new SingleLineRule("\"", "\"", COMMENT_TOKEN),
      endofsentence
    };
    return rules;
  }

  /** {@inheritDoc} */
  @Override
  public IRule[] getParsingRules() {
    if (parsingRules == null) {
      parsingRules = initParsingRules();
    }
    return parsingRules;
  }

  /** {@inheritDoc} */
  @Override
  public boolean isErrorMsg(final String s) {
    return s.matches("Error.*") || s.matches("Invalid module name.*");
  }


  /** {@inheritDoc} */
  @Override
  public String[] getIdeCommand(final String ide, final String[] path, 
                                final String file) {
    final String [] cmds = new String[1 + (path.length * 2) + 1];
    cmds[0] = ide;
    for (int i = 0; i < path.length; i++) {
      cmds[(i * 2) + 1] = "-I";
      cmds[(i * 2) + 2] = path[i];
    }
    cmds[cmds.length - 1] = file;
    return cmds;
  }

  /** {@inheritDoc} */
  @Override
  public String[] getCompilingCommand(final String ide, 
                                      final String[] p, 
                                      final String file) {
    String [] path = p;
    if (path == null) {
      path = new String[0];
    }
    final String [] cmds = new String[1 + (path.length * 2) + 1];
    cmds[0] = ide;
    for (int i = 0; i < path.length; i++) {
      cmds[(i * 2) + 1] = "-I";
      cmds[(i * 2) + 2] = path[i];
    }
    //cmds[cmds.length - 2] = "-compile";
    cmds[cmds.length - 1] = file.substring(0, file.length() - 2);
    return cmds;
  }

  
  public Image createImage(final String path) {
    final InputStream is = this.getClass().getClassLoader().getResourceAsStream(path);
    final Image img = new Image(PlatformUI.getWorkbench().getDisplay(), is);
    return img;
  }
  
  /** {@inheritDoc} */
  @Override
  public ProverType getFileOutline(final ProverEditor ed, 
                                   final IDocument doc, 
                                   final ProverType root) {

    if (imgs == null) {
      final Image [] tab = {
          createImage("/icons/module.gif"),
          createImage("/icons/moduleb.gif"),
          createImage("/icons/sections.gif"),
          createImage("/icons/defs1.gif"),
          createImage("/icons/defs2.gif"),
          createImage("/icons/defs3.gif"),
          createImage("/icons/defs4.gif"),
          createImage("/icons/defs5.gif"),
          createImage("/icons/defs6.gif"),
          createImage("/icons/defs7.gif"),
          createImage("/icons/defs8.gif")
      };
      imgs = tab;
    }
    final CoqConstructFinder ccf = new CoqConstructFinder(ed, doc);
    
    ccf.parse(root);
    return root;
  }
  

  /** {@inheritDoc} */
  @Override
  public Pattern [][] getTagPatterns() {
    return pats;
  }

}
