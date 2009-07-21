package mobius.cct.tools;

/**
 * Interface of tools run from the command line.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Tool {
  /**
   * Entry point.
   * @param env Environment.
   */
  void main(Environment env);
  
  /**
   * Get description of this tool.
   * @param env Environment.
   * @return Short description.
   */
  String getDescription(Environment env);
}
