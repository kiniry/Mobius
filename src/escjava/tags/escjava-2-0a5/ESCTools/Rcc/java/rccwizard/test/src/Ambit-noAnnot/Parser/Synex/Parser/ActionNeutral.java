// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Parser;

import Parser.Synex.SynexException;
import Parser.Synex.Parser.Parser;
import Parser.Synex.Parser.Outcome;
import Parser.Synex.Scanner.Location;

public class ActionNeutral extends Action {

  public static Action neutral = new ActionNeutral();

  public ActionNeutral() {
    super();
  }

  public Outcome exec(Parser parser, Outcome outcome, 
      Location begLocation, Location endLocation) {
    return outcome;
  }

}
