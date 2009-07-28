// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Parser;

import Parser.Synex.SynexException;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Location;
import Parser.Synex.Grammar.BadGrammarException;

public class ActionFetch extends Action {

  public static Action fetch0 = new ActionFetch(0);
  public static Action fetch1 = new ActionFetch(1);
  public static Action fetch2 = new ActionFetch(2);
  public static Action fetch3 = new ActionFetch(3);
  public static Action fetch4 = new ActionFetch(4);
  public static Action fetch5 = new ActionFetch(5);
  public static Action fetch6 = new ActionFetch(6);
  public static Action fetch7 = new ActionFetch(7);

  int n;

  public ActionFetch(int n) {
    super();
    this.n = n;
  }

  public Outcome exec(Parser parser, Outcome outcome, 
      Location begLocation, Location endLocation) throws BadGrammarException {
    return parser.fetch(n);
  }

}
