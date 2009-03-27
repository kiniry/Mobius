package freeboogie.experiments.graphgen.clops;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;

public class GraphGenOptionStore extends OptionStore implements GraphGenOptionsInterface {

  private final ie.ucd.clops.runtime.options.IntegerOption max_depthOG;
  private final ie.ucd.clops.runtime.options.IntegerOption max_nodesOG;
  private final ie.ucd.clops.runtime.options.FloatOption probability_splitOG;
  private final ie.ucd.clops.runtime.options.FloatOption probability_linkOG;
  private final ie.ucd.clops.runtime.options.FloatOption probability_readOG;
  private final ie.ucd.clops.runtime.options.FloatOption probability_writeOG;
  private final ie.ucd.clops.runtime.options.FileOption dot_output_fileOG;
  private final ie.ucd.clops.runtime.options.FileOption boogie_output_fileOG;
  private final ie.ucd.clops.runtime.options.IntegerOption seedOG;
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
    probability_splitOG = new ie.ucd.clops.runtime.options.FloatOption("probability_split", "(?:-ps)");
    addOption(probability_splitOG);
    probability_splitOG.setProperty("minvalue", "0");
    probability_splitOG.setProperty("default", "0.3");
    probability_splitOG.setProperty("description", "Probability of splitting for a generative step.");
    probability_linkOG = new ie.ucd.clops.runtime.options.FloatOption("probability_link", "(?:-pl)");
    addOption(probability_linkOG);
    probability_linkOG.setProperty("minvalue", "0");
    probability_linkOG.setProperty("default", "0.6");
    probability_linkOG.setProperty("description", "Probability of growing a link for a generative step.");
    probability_readOG = new ie.ucd.clops.runtime.options.FloatOption("probability_read", "(?:-pr)");
    addOption(probability_readOG);
    probability_readOG.setProperty("minvalue", "0");
    probability_readOG.setProperty("default", "0.3");
    probability_readOG.setProperty("description", "Probability of a node being a read.");
    probability_writeOG = new ie.ucd.clops.runtime.options.FloatOption("probability_write", "(?:-pw)");
    addOption(probability_writeOG);
    probability_writeOG.setProperty("minvalue", "0");
    probability_writeOG.setProperty("default", "0.3");
    probability_writeOG.setProperty("description", "Probability of a node being a write.");
    dot_output_fileOG = new ie.ucd.clops.runtime.options.FileOption("dot_output_file", "(?:-do)");
    addOption(dot_output_fileOG);
    dot_output_fileOG.setProperty("canbedir", "false");
    dot_output_fileOG.setProperty("description", "Output file for .dot representation of the graph.");
    boogie_output_fileOG = new ie.ucd.clops.runtime.options.FileOption("boogie_output_file", "(?:-bo)");
    addOption(boogie_output_fileOG);
    boogie_output_fileOG.setProperty("canbedir", "false");
    boogie_output_fileOG.setProperty("description", "Output file for boogie generated code.");
    seedOG = new ie.ucd.clops.runtime.options.IntegerOption("seed", "(?:-s)|(?:--seed)");
    addOption(seedOG);
    seedOG.setProperty("description", "The seed used for random number generation.");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup optionOG = new OptionGroup("option");
    addOptionGroup(optionOG);
    //Setup groupings
    optionOG.addOptionOrGroup(max_depthOG);
    optionOG.addOptionOrGroup(max_nodesOG);
    optionOG.addOptionOrGroup(dot_output_fileOG);
    optionOG.addOptionOrGroup(probability_linkOG);
    optionOG.addOptionOrGroup(probability_splitOG);
    optionOG.addOptionOrGroup(probability_readOG);
    optionOG.addOptionOrGroup(probability_writeOG);
    optionOG.addOptionOrGroup(boogie_output_fileOG);
    optionOG.addOptionOrGroup(seedOG);
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
  
// Option probability_split.
// Aliases: [-ps]
  
  /**
   * {@inheritDoc}
   */
  public boolean isprobability_splitSet() {
    return probability_splitOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public float getprobability_split() {
    return probability_splitOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public float getRawprobability_split() {
    return probability_splitOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FloatOption getprobability_splitOption() {
    return probability_splitOG;
  }
  
// Option probability_link.
// Aliases: [-pl]
  
  /**
   * {@inheritDoc}
   */
  public boolean isprobability_linkSet() {
    return probability_linkOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public float getprobability_link() {
    return probability_linkOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public float getRawprobability_link() {
    return probability_linkOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FloatOption getprobability_linkOption() {
    return probability_linkOG;
  }
  
// Option probability_read.
// Aliases: [-pr]
  
  /**
   * {@inheritDoc}
   */
  public boolean isprobability_readSet() {
    return probability_readOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public float getprobability_read() {
    return probability_readOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public float getRawprobability_read() {
    return probability_readOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FloatOption getprobability_readOption() {
    return probability_readOG;
  }
  
// Option probability_write.
// Aliases: [-pw]
  
  /**
   * {@inheritDoc}
   */
  public boolean isprobability_writeSet() {
    return probability_writeOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public float getprobability_write() {
    return probability_writeOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public float getRawprobability_write() {
    return probability_writeOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FloatOption getprobability_writeOption() {
    return probability_writeOG;
  }
  
// Option dot_output_file.
// Aliases: [-do]
  
  /**
   * {@inheritDoc}
   */
  public boolean isdot_output_fileSet() {
    return dot_output_fileOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getdot_output_file() {
    return dot_output_fileOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawdot_output_file() {
    return dot_output_fileOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getdot_output_fileOption() {
    return dot_output_fileOG;
  }
  
// Option boogie_output_file.
// Aliases: [-bo]
  
  /**
   * {@inheritDoc}
   */
  public boolean isboogie_output_fileSet() {
    return boogie_output_fileOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getboogie_output_file() {
    return boogie_output_fileOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawboogie_output_file() {
    return boogie_output_fileOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getboogie_output_fileOption() {
    return boogie_output_fileOG;
  }
  
// Option seed.
// Aliases: [-s, --seed]
  
  /**
   * {@inheritDoc}
   */
  public boolean isseedSet() {
    return seedOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public int getseed() {
    return seedOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public int getRawseed() {
    return seedOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.IntegerOption getseedOption() {
    return seedOG;
  }
  
}
