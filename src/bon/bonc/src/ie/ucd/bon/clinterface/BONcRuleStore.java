package ie.ucd.bon.clinterface;

import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.Action;
import ie.ucd.clops.runtime.rules.Expression;
import ie.ucd.clops.runtime.rules.FlyRule;
import ie.ucd.clops.runtime.rules.OverrideRule;
import ie.ucd.clops.runtime.rules.RuleStore;
import ie.ucd.clops.runtime.rules.ValidityRule;


import java.util.Arrays;
import java.util.List;

/**
 * The rule store is used to handle the constraints and the validity
 * checks associated with the options.
 * @author The CLOPS team (kind@ucd.ie)
 */
public class BONcRuleStore extends RuleStore {
  
  public BONcRuleStore() {
    Expression<Boolean> rule1Condition = new Rule1Condition();
    FlyRule rule1 = new FlyRule("Formal",rule1Condition);
    addFlyRule("Formal", rule1);
    rule1.addAction(new Action<Boolean>("CheckFormal", new Rule1Expression1()));
    rule1.addAction(new Action<Boolean>("CheckInformal", new Rule1Expression2()));
    rule1.addAction(new Action<Boolean>("CheckConsistency", new Rule1Expression3()));
    Expression<Boolean> rule2Condition = new Rule2Condition();
    FlyRule rule2 = new FlyRule("Informal",rule2Condition);
    addFlyRule("Informal", rule2);
    rule2.addAction(new Action<Boolean>("CheckInformal", new Rule2Expression4()));
    rule2.addAction(new Action<Boolean>("CheckFormal", new Rule2Expression5()));
    rule2.addAction(new Action<Boolean>("CheckConsistency", new Rule2Expression6()));
    rule2.addAction(new Action<Boolean>("Typecheck", new Rule2Expression7()));
    Expression<Boolean> rule3Condition = new Rule3Condition();
    FlyRule rule3 = new FlyRule("PrettyPrint",rule3Condition);
    addFlyRule("PrettyPrint", rule3);
    rule3.addAction(new Action<String>("Print", new Rule3Expression8()));
    Expression<Boolean> rule4Condition = new Rule4Condition();
    FlyRule rule4 = new FlyRule("CheckFormal",rule4Condition);
    addFlyRule("CheckFormal", rule4);
    rule4.addAction(new Action<Boolean>("Typecheck", new Rule4Expression9()));
    Expression<Boolean> rule5Condition = new Rule5Condition();
    ValidityRule rule5 = new ValidityRule(rule5Condition);
    rule5.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule5Expression()));
    addValidityRule(rule5);
    Expression<Boolean> rule6Condition = new Rule6Condition();
    ValidityRule rule6 = new ValidityRule(rule6Condition);
    rule6.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule6Expression()));
    addValidityRule(rule6);
  }

  public static class Rule1Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Formal")).getValue();
    }
  }
    
  public static class Rule1Expression1 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return true;
    }
  }
  
  public static class Rule1Expression2 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return false;
    }
  }
  
  public static class Rule1Expression3 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return false;
    }
  }
  
  public static class Rule2Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Informal")).getValue();
    }
  }
    
  public static class Rule2Expression4 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return true;
    }
  }
  
  public static class Rule2Expression5 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return false;
    }
  }
  
  public static class Rule2Expression6 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return false;
    }
  }
  
  public static class Rule2Expression7 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return false;
    }
  }
  
  public static class Rule3Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("PrettyPrint")).getValue();
    }
  }
    
  public static class Rule3Expression8 implements Expression<String> {
    /**
     * {@inheritDoc}
     */
    public String evaluate(OptionStore optionStore) {
      return "TXT";
    }
  }
  
  public static class Rule4Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return !((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("CheckFormal")).hasValue();
    }
  }
    
  public static class Rule4Expression9 implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(OptionStore optionStore) {
      return false;
    }
  }
  
  public static class Rule5Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.EnumOption)optionStore.getOptionByIdentifier("Print")).hasValue() && !((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("PrintOutput")).hasValue();
    }
  }
    
  public static class Rule5Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("Output file (-po) for printing must be provided.");
    }
  }
  
  public static class Rule6Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return !((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Version")).getValue() && !((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("Help")).getValue() && !((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("PrintMan")).getValue() && !((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("PrintReadme")).getValue() && !((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("PrintBashCompletion")).getValue() && 
 !((ie.ucd.clops.runtime.options.BooleanOption)optionStore.getOptionByIdentifier("ReadFromStdin")).getValue() && (((ie.ucd.clops.runtime.options.FileListOption)optionStore.getOptionByIdentifier("SourceFiles")).getValue().size() == 0);
    }
  }
    
  public static class Rule6Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("Must provide at least one source file or read from standard input.");
    }
  }
  

  protected final boolean shouldApplyFlyRulesTransitively() {
    return false;
  }
}
