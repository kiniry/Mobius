// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Parser;

/** An outcome representing parsing success. */

import Parser.Synex.Parser.Outcome;

public class ParseSuccess extends Outcome {

  public static ParseSuccess parseSuccess = new ParseSuccess();

  public ParseSuccess() {}

}
