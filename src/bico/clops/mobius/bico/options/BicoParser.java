package mobius.bico.options;

import ie.ucd.clops.runtime.parser.AbstractSpecificCLParser;
import ie.ucd.clops.runtime.rules.RuleStore;

public class BicoParser extends AbstractSpecificCLParser { 
  private final BicoOptionStore optionStore;
  private final ie.ucd.clops.runtime.rules.RuleStore ruleStore;

  public BicoParser() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    optionStore = new BicoOptionStore();
    ruleStore = new BicoRuleStore(); 
  }

  public BicoOptionStore getOptionStore() {
    return optionStore;  
  }
  
  public RuleStore getRuleStore() {
    return ruleStore;
  }
  
  public String getFormatString() {
    return "(Option | Class)* Dir (Option | Class)*"; 
  }
}