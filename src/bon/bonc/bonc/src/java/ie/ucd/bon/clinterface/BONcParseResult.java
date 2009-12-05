package ie.ucd.bon.clinterface;

import ie.ucd.clops.runtime.errors.ParseResult;

/**
 * A parse result for the BONcParser.
 * @author The CLOPS team
 */
public class BONcParseResult extends ParseResult {

  private BONcOptionStore optionStore;

  public BONcParseResult(ParseResult parseResult, BONcOptionStore optionStore) {
    super(parseResult);
    this.optionStore = optionStore;
  }

  public BONcOptionStore getOptionStore() {
    return optionStore;
  }

} 