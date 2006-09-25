// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Parser;

import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Location;
import Parser.Synex.SynexException;

public abstract class Action {

  /** Produce a client-defined parsing outcome as a result of parsing a production.
      The outcome argument is the outcome of the production rhs. The action may also
      examine the parser stack by parser.fetch(n). (The contents of the parser stack are set
      by Store grammars.) The locations could be inserted into a (subclasses of) OutcomeLocated 
      results to record the origins of user-defined data structures. 
      Should return a ParseFailure outcome to give errors. User-action exceptions should be
      subclasses of SynexException. "null" can be returned as a successful outcome. */
  public abstract Outcome exec(Parser parser, Outcome outcome, 
    Location beg, Location end) throws SynexException;

}
