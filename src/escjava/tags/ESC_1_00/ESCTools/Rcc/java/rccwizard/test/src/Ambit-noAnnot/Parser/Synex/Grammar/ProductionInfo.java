// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Grammar;

import Parser.Synex.Parser.Outcome;

public class ProductionInfo extends Outcome {

  public String productionName; // just for error reporting
  public int frameSize;
  public int argsNo;

  public ProductionInfo(String productionName, int frameSize, int argsNo) {
    super();
    this.productionName = productionName;
    this.frameSize = frameSize;
    this.argsNo = argsNo;
  }
  
}
