package fr.inria.everest.coq.editor.utils;

import java.util.LinkedList;

import mobius.prover.gui.editor.BasicRuleScanner;
import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.SingleLineRule;

import fr.inria.everest.coq.editor.utils.types.CoqType;
import fr.inria.everest.coq.editor.utils.types.token.TypeToken;
import fr.inria.everest.coq.editor.utils.types.token.data.ATokenData;
import fr.inria.everest.coq.editor.utils.types.token.data.ComplexBegin;
import fr.inria.everest.coq.editor.utils.types.token.data.ComplexEnd;
import fr.inria.everest.coq.editor.utils.types.token.data.Simple;

public class CoqConstructFinder implements ICoqColorConstants{
  int fOffset;
  int fOffsetEnd;
  IDocument fDoc;
  private BasicRuleScanner fScanner;
  private ProverEditor fEditor;
  
  
  public CoqConstructFinder(ProverEditor editor, IDocument doc) {
    fDoc = doc;
    fOffset = 0;
    fOffsetEnd = fDoc.getLength();
    fScanner = new BasicRuleScanner(this.getRules());
    fEditor = editor;

    fScanner.setRange(doc, fOffset, fOffsetEnd);
  }
  public CoqConstructFinder(ProverEditor editor, IDocument doc, int startOffset, int endOffset) {
    this(editor, doc);
    fOffset = startOffset;
    fOffsetEnd = endOffset;

    fScanner.setRange(doc, startOffset, endOffset);
    
  }

  public ProverType parse(ProverType root) {
    IToken tok;
    LinkedList tokens = new LinkedList();
    do {
      tok = fScanner.nextToken();
      if(tok.isOther() && tok.getData() instanceof ATokenData) {
        ATokenData data = (ATokenData)tok.getData();  
        tokens.addLast(data.spawn(fDoc, fScanner));
        //System.out.println(tokens.getFirst());
      }
    } while (!tok.isEOF());
    //tokens.removeLast();
    
    while(tokens.size() > 0) {
      ATokenData data = (ATokenData)tokens.removeFirst();

      if(data instanceof Simple) {
        
        ProverType pt = data.parse(fEditor);
        root.add(pt);
      }
      else if (data instanceof ComplexBegin) {
        ProverType pt = getComplex((ComplexBegin)data, tokens);
        root.add(pt);
      }
      else {
        // Ignore it.. it should not happen
      }
    }
    return root;
  }
  public ProverType getComplex(ComplexBegin begin, LinkedList tokens) {
    
    CoqType root =(CoqType) begin.parse(fEditor);
    while(tokens.size() > 0) {
      ATokenData data = (ATokenData)tokens.removeFirst();
      if(data instanceof Simple) {        
        ProverType pt = data.parse(fEditor);
        root.add(pt);
      }
      else if (data instanceof ComplexBegin) {
        ProverType pt = getComplex((ComplexBegin)data, tokens);
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
