// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

/** An environment mapping non-terminal names to grammars. */

import Parser.Synex.Grammar.Grammar;

public class GrammarList {

  public Grammar first;
  public GrammarList next;

  public GrammarList(Grammar first, GrammarList next) {
    this.first = first; this.next = next;
  }
  
  public GrammarList(Grammar g1) {
    this.first = g1; this.next = null;
  }
  public GrammarList(Grammar g1, Grammar g2) {
    this.first = g1; this.next = new GrammarList(g2);
  }
  public GrammarList(Grammar g1, Grammar g2, Grammar g3) {
    this.first = g1; this.next = new GrammarList(g2, g3);
  }
  public GrammarList(Grammar g1, Grammar g2, Grammar g3, Grammar g4) {
    this.first = g1; this.next = new GrammarList(g2, g3, g4);
  }
  public GrammarList(Grammar g1, Grammar g2, Grammar g3, Grammar g4,
                     Grammar g5) {
    this.first = g1; this.next = new GrammarList(g2, g3, g4, g5);
  }
  public GrammarList(Grammar g1, Grammar g2, Grammar g3, Grammar g4,
                     Grammar g5, Grammar g6) {
    this.first = g1; this.next = new GrammarList(g2, g3, g4, g5, g6);
  }
  public GrammarList(Grammar g1, Grammar g2, Grammar g3, Grammar g4,
                     Grammar g5, Grammar g6, Grammar g7) {
    this.first = g1; this.next = new GrammarList(g2, g3, g4, g5, g6, g7);
  }
  public GrammarList(Grammar g1, Grammar g2, Grammar g3, Grammar g4,
                     Grammar g5, Grammar g6, Grammar g7, Grammar g8) {
    this.first = g1; this.next = new GrammarList(g2, g3, g4, g5, g6, g7, g8);
  }
  public GrammarList(Grammar g1, Grammar g2, Grammar g3, Grammar g4,
                     Grammar g5, Grammar g6, Grammar g7, Grammar g8,
                     GrammarList g) {
    this.first = g1;
    this.next =
      new GrammarList(g2, new GrammarList(g3, new GrammarList(g4, 
      new GrammarList(g5, new GrammarList(g6, new GrammarList(g7, 
      new GrammarList(g8, g)))))));
  }
   
}
