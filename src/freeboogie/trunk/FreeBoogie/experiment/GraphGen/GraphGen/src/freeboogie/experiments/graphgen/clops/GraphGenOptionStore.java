package freeboogie.experiments.graphgen.clops;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;

public class GraphGenOptionStore extends OptionStore implements GraphGenOptionsInterface {

  private final ie.ucd.clops.runtime.options.IntegerOption max_depthOG;
  private final ie.ucd.clops.runtime.options.IntegerOption max_nodesOG;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public GraphGenOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {

    //Options
    max_depthOG = new ie.ucd.clops.runtime.options.IntegerOption("max_depth", "(?:-d)|(?:--depth)");
    addOption(max_depthOG);
    max_depthOG.setProperty("minvalue", "0");
    max_depthOG.setProperty("default", "10");
    max_depthOG.setProperty("description", "Maximum number of generation steps before returning a single node.");
    max_nodesOG = new ie.ucd.clops.runtime.options.IntegerOption("max_nodes", "(?:-n)|(?:--max-nodes)");
    addOption(max_nodesOG);
    max_nodesOG.setProperty("minvalue", "1");
    max_nodesOG.setProperty("default", "100000");
    max_nodesOG.setProperty("description", "Maximum number of nodes to produce. Actual number produced will always be somewhat larger.");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup optionOG = new OptionGroup("option");
    addOptionGroup(optionOG);
    //Setup groupings
    optionOG.addOptionOrGroup(max_depthOG);
    optionOG.addOptionOrGroup(max_nodesOG);
  }
  
// Option max_depth.
// Aliases: [-d, --depth]
  
  /**
   * {@inheritDoc}
   */
  public boolean ismax_depthSet() {
    return max_depthOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public int getmax_depth() {
    return max_depthOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public int getRawmax_depth() {
    return max_depthOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.IntegerOption getmax_depthOption() {
    return max_depthOG;
  }
  
// Option max_nodes.
// Aliases: [-n, --max-nodes]
  
  /**
   * {@inheritDoc}
   */
  public boolean ismax_nodesSet() {
    return max_nodesOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public int getmax_nodes() {
    return max_nodesOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public int getRawmax_nodes() {
    return max_nodesOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.IntegerOption getmax_nodesOption() {
    return max_nodesOG;
  }
  
}
