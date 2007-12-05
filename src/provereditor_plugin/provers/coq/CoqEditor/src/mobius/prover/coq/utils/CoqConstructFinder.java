package mobius.prover.coq.utils;

import java.util.LinkedList;

import mobius.prover.coq.utils.types.CoqType;
import mobius.prover.coq.utils.types.token.TypeToken;
import mobius.prover.coq.utils.types.token.data.ATokenData;
import mobius.prover.coq.utils.types.token.data.ComplexBegin;
import mobius.prover.coq.utils.types.token.data.ComplexEnd;
import mobius.prover.coq.utils.types.token.data.Simple;
import mobius.prover.gui.editor.BasicRuleScanner;
import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;


public class CoqConstructFinder implements ICoqColorConstants {
  private int fOffset;
  private int fOffsetEnd;
  private IDocument fDoc;
  private BasicRuleScanner fScanner;
  private ProverEditor fEditor;
  
  
  public CoqConstructFinder(final ProverEditor editor, final IDocument doc) {
    fDoc = doc;
    fOffset = 0;
    fOffsetEnd = fDoc.getLength();
    fScanner = new BasicRuleScanner(this.getRules());
    fEditor = editor;

    fScanner.setRange(doc, fOffset, fOffsetEnd);
  }
  public CoqConstructFinder(final ProverEditor editor, final IDocument doc, 
                            final int startOffset, final int endOffset) {
    this(editor, doc);
    fOffset = startOffset;
    fOffsetEnd = endOffset;

    fScanner.setRange(doc, startOffset, endOffset);
    
  }

  public ProverType parse(final ProverType root) {
    IToken tok;
    final LinkedList<ATokenData> tokens = new LinkedList<ATokenData>();
    do {
      tok = fScanner.nextToken();
      if (tok.isOther() && tok.getData() instanceof ATokenData) {
        final ATokenData data = (ATokenData)tok.getData();  
        tokens.addLast(data.spawn(fDoc, fScanner));
        //System.out.println(tokens.getFirst());
      }
    } while (!tok.isEOF());
    //tokens.removeLast();
    
    while (tokens.size() > 0) {
      final ATokenData data = (ATokenData)tokens.removeFirst();

      if (data instanceof Simple) {
        
        final ProverType pt = data.parse(fEditor);
        root.add(pt);
      }
      else if (data instanceof ComplexBegin) {
        final ProverType pt = getComplex((ComplexBegin)data, tokens);
        root.add(pt);
      }
      else {
        // Ignore it.. it should not happen
      }
    }
    return root;
  }
  public ProverType getComplex(final ComplexBegin begin, 
                               final LinkedList<ATokenData> tokens) {
    
    final CoqType root = (CoqType) begin.parse(fEditor);
    while (tokens.size() > 0) {
      final ATokenData data = tokens.removeFirst();
      if (data instanceof Simple) {        
        final ProverType pt = data.parse(fEditor);
        root.add(pt);
      }
      else if (data instanceof ComplexBegin) {
        final ProverType pt = getComplex((ComplexBegin)data, tokens);
        root.add(pt);
      }
      else {
        root.setEnd(data.getEnd());
        return root;
      }
    }
    return root;
  }
  public int getDocumentLength() {
    return fDoc.getLength();
  }
  public IDocument getDocument() {
    return fDoc;
  }
  
  final TypeToken module = new TypeToken(new ComplexBegin());
  final TypeToken endmodule = new TypeToken(new ComplexEnd());
  final TypeToken declare = new TypeToken(new Simple());
  
  private IRule [] getRules() {
    final IRule [] rules = {
      new MultiLineRule("(*", "*)", comment),
      new MultiLineRule("\"", "\"", string),
      new SingleLineRule("(*", "*)", comment),
      new SingleLineRule("\"", "\"", string),
      new MultiLineRule("Declare ", ".", declare),
      new MultiLineRule("Variable ", ".", declare),
      new MultiLineRule("Hypothesis ", ".", declare),
      new MultiLineRule("Record ", ".", declare),
      new PatternRuleTaboo("Module ", ".", module),
      new PatternRuleTaboo("Section ", ".", module),
      new PatternRuleTaboo("Parameter ", ":", declare),
      new MultiLineRule("Definition ", ".", declare),
      new MultiLineRule("Axiom ", ".", declare),
      new MultiLineRule("Fixpoint ", ".", declare),
      new SingleLineRule("Module ", ":=", declare),
      new SingleLineRule("Let ", ":=", declare),

      new SingleLineRule("Theorem ", ".", declare),
      new SingleLineRule("Lemma ", ".", declare),
      new MultiLineRule("Inductive ", ":=", declare),
      new MultiLineRule("Scheme ", ":=", declare),
      new MultiLineRule("Parameter ", ":=", declare),
      new MultiLineRule("End ", ".", endmodule)
    };
    return rules;
  }
}
