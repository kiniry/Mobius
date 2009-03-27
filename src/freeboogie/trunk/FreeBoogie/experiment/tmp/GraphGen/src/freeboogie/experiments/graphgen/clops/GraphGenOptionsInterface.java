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
  

// Option probability_split. 
// Aliases: [-ps]

  /**
   * @return true if the option probability_split has been used
   * in the command line.
   */
  boolean isprobability_splitSet();
  
  /**
   * Get the value of {@code Option} probability_split.
   * @return the value of the option probability_split if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  float getprobability_split();
  

// Option probability_link. 
// Aliases: [-pl]

  /**
   * @return true if the option probability_link has been used
   * in the command line.
   */
  boolean isprobability_linkSet();
  
  /**
   * Get the value of {@code Option} probability_link.
   * @return the value of the option probability_link if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  float getprobability_link();
  

// Option probability_read. 
// Aliases: [-pr]

  /**
   * @return true if the option probability_read has been used
   * in the command line.
   */
  boolean isprobability_readSet();
  
  /**
   * Get the value of {@code Option} probability_read.
   * @return the value of the option probability_read if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  float getprobability_read();
  

// Option probability_write. 
// Aliases: [-pw]

  /**
   * @return true if the option probability_write has been used
   * in the command line.
   */
  boolean isprobability_writeSet();
  
  /**
   * Get the value of {@code Option} probability_write.
   * @return the value of the option probability_write if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  float getprobability_write();
  

// Option dot_output_file. 
// Aliases: [-do]

  /**
   * @return true if the option dot_output_file has been used
   * in the command line.
   */
  boolean isdot_output_fileSet();
  
  /**
   * Get the value of {@code Option} dot_output_file.
   * @return the value of the option dot_output_file if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getdot_output_file();
  

// Option boogie_output_file. 
// Aliases: [-bo]

  /**
   * @return true if the option boogie_output_file has been used
   * in the command line.
   */
  boolean isboogie_output_fileSet();
  
  /**
   * Get the value of {@code Option} boogie_output_file.
   * @return the value of the option boogie_output_file if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getboogie_output_file();
  
}
