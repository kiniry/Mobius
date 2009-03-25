package freeboogie.experiments.graphgen.clops;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface GraphGenOptionsInterface {


// Option max_depth. 
// Aliases: [-d, --depth]

  /**
   * @return true if the option max_depth has been used
   * in the command line.
   */
  boolean ismax_depthSet();
  
  /**
   * Get the value of {@code Option} max_depth.
   * @return the value of the option max_depth if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  int getmax_depth();
  

// Option max_nodes. 
// Aliases: [-n, --max-nodes]

  /**
   * @return true if the option max_nodes has been used
   * in the command line.
   */
  boolean ismax_nodesSet();
  
  /**
   * Get the value of {@code Option} max_nodes.
   * @return the value of the option max_nodes if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  int getmax_nodes();
  
}
